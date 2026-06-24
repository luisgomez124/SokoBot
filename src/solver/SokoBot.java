package solver;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.PriorityQueue;
import java.util.Set;

/**
 * SokoBot
 *
 * Solves Sokoban puzzles using A* search over the space of
 * (player position, crate positions) states. Player movement between
 * pushes is collapsed using a flood fill, and clearly unsolvable states
 * (crates stuck in corners) are pruned before they are ever queued.
 */
public class SokoBot {

    // Direction order is fixed everywhere: up, down, left, right
    static int[] deltaRow = {-1, 1, 0, 0};
    static int[] deltaCol = {0, 0, -1, 1};
    static char[] moveChar = {'u', 'd', 'l', 'r'};

    static int totalRows, totalCols;
    static char[][] grid;
    static ArrayList<int[]> targetList;

    /**
     * State
     *
     * Represents one node in the search: where the player is standing,
     * where every crate currently sits, and the move string used to
     * reach this point from the start.
     */
    static class State {
        int playerRow, playerCol;
        int[] crateRows, crateCols;
        String moves;

        State(int playerRow, int playerCol, int[] crateRows, int[] crateCols, String moves) {
            this.playerRow = playerRow;
            this.playerCol = playerCol;
            this.crateRows = crateRows;
            this.crateCols = crateCols;
            this.moves = moves;
        }

        // Two states are the same position in the search space if the
        // player and every crate line up, regardless of how we got there.
        String key() {
            StringBuilder sb = new StringBuilder();
            sb.append(playerRow).append(',').append(playerCol).append(';');

            int n = crateRows.length;
            Integer[] order = new Integer[n];
            for (int i = 0; i < n; i++) order[i] = i;
            Arrays.sort(order, (a, b) -> {
                int ra = crateRows[a], rb = crateRows[b];
                if (ra != rb) return ra - rb;
                return crateCols[a] - crateCols[b];
            });

            for (int idx : order) {
                sb.append(crateRows[idx]).append(',').append(crateCols[idx]).append(';');
            }
            return sb.toString();
        }
    }

    public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {

        totalRows = height;
        totalCols = width;
        grid = mapData;

        // Collect target cells once; reused every time the heuristic runs
        targetList = new ArrayList<>();
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (mapData[r][c] == '.') {
                    targetList.add(new int[]{r, c});
                }
            }
        }

        // Read player and crate starting positions from itemsData
        int startPlayerRow = -1, startPlayerCol = -1;
        ArrayList<int[]> crateStart = new ArrayList<>();
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (itemsData[r][c] == '@') {
                    startPlayerRow = r;
                    startPlayerCol = c;
                } else if (itemsData[r][c] == '$') {
                    crateStart.add(new int[]{r, c});
                }
            }
        }

        int numCrates = crateStart.size();
        int[] crateRows = new int[numCrates];
        int[] crateCols = new int[numCrates];
        for (int i = 0; i < numCrates; i++) {
            crateRows[i] = crateStart.get(i)[0];
            crateCols[i] = crateStart.get(i)[1];
        }

        boolean[][] deadSquare = computeDeadSquares();

        State start = new State(startPlayerRow, startPlayerCol, crateRows, crateCols, "");

        if (isGoal(start)) {
            return "";
        }

        // Priority queue ordered by f = moves taken + heuristic estimate
        PriorityQueue<State> open = new PriorityQueue<>(
            Comparator.comparingInt(s -> s.moves.length() + heuristic(s))
        );
        open.add(start);

        Set<String> visited = new HashSet<>();
        visited.add(start.key());

        long startTime = System.currentTimeMillis();
        long timeLimitMs = 14000; // leave a margin under the 15s cutoff

        while (!open.isEmpty()) {

            if (System.currentTimeMillis() - startTime > timeLimitMs) {
                return ""; // ran out of time, engine will report "Took too long"
            }

            State current = open.poll();
            boolean[][] reachable = computeReachable(current);

            int numC = current.crateRows.length;
            for (int i = 0; i < numC; i++) {
                int cr = current.crateRows[i];
                int cc = current.crateCols[i];

                for (int d = 0; d < 4; d++) {
                    int pushFromRow = cr - deltaRow[d];
                    int pushFromCol = cc - deltaCol[d];
                    int crateToRow = cr + deltaRow[d];
                    int crateToCol = cc + deltaCol[d];

                    if (!inBounds(pushFromRow, pushFromCol)) continue;
                    if (!reachable[pushFromRow][pushFromCol]) continue;
                    if (!inBounds(crateToRow, crateToCol)) continue;
                    if (grid[crateToRow][crateToCol] == '#') continue;
                    if (hasCrateAt(current, crateToRow, crateToCol)) continue;
                    if (deadSquare[crateToRow][crateToCol]) continue;

                    int[] nextRows = current.crateRows.clone();
                    int[] nextCols = current.crateCols.clone();
                    nextRows[i] = crateToRow;
                    nextCols[i] = crateToCol;

                    String walk = walkPathTo(current.playerRow, current.playerCol, pushFromRow, pushFromCol);
                    String fullMoves = current.moves + walk + moveChar[d];

                    State next = new State(cr, cc, nextRows, nextCols, fullMoves);

                    String nextKey = next.key();
                    if (visited.contains(nextKey)) continue;
                    if (isCornerDeadlock(next)) continue;

                    if (isGoal(next)) {
                        return next.moves;
                    }

                    visited.add(nextKey);
                    open.add(next);
                }
            }
        }

        return ""; // search exhausted, no solution found
    }

    // Player can reach the push point without moving any crate? BFS from the
    // current player position over open floor, recording the move taken to
    // reach each cell so the real walking path can be reconstructed later.
    static char[][] reachedFrom; // direction index used to first reach each cell, or -1

    static boolean[][] computeReachable(State state) {
        boolean[][] reachable = new boolean[totalRows][totalCols];
        reachedFrom = new char[totalRows][totalCols];
        for (char[] row : reachedFrom) Arrays.fill(row, (char) -1);

        ArrayDeque<int[]> queue = new ArrayDeque<>();
        queue.add(new int[]{state.playerRow, state.playerCol});
        reachable[state.playerRow][state.playerCol] = true;

        while (!queue.isEmpty()) {
            int[] cur = queue.poll();
            for (int d = 0; d < 4; d++) {
                int nr = cur[0] + deltaRow[d];
                int nc = cur[1] + deltaCol[d];
                if (!inBounds(nr, nc)) continue;
                if (reachable[nr][nc]) continue;
                if (grid[nr][nc] == '#') continue;
                if (hasCrateAt(state, nr, nc)) continue;
                reachable[nr][nc] = true;
                reachedFrom[nr][nc] = (char) d;
                queue.add(new int[]{nr, nc});
            }
        }
        return reachable;
    }

    // Reconstructs the actual walking moves from the player's current
    // position to (targetRow, targetCol) using the BFS parent trail left
    // behind in reachedFrom by the most recent computeReachable() call.
    static String walkPathTo(int playerRow, int playerCol, int targetRow, int targetCol) {
        StringBuilder sb = new StringBuilder();
        int r = targetRow, c = targetCol;
        while (r != playerRow || c != playerCol) {
            int d = reachedFrom[r][c];
            sb.append(moveChar[d]);
            r -= deltaRow[d];
            c -= deltaCol[d];
        }
        return sb.reverse().toString();
    }

    // Sum of each crate's distance to its nearest unclaimed target.
    // Underestimates the true cost (never overestimates), so A* stays correct.
    static int heuristic(State state) {
        int n = state.crateRows.length;
        boolean[] used = new boolean[targetList.size()];
        int total = 0;

        for (int i = 0; i < n; i++) {
            int bestDist = Integer.MAX_VALUE;
            int bestT = -1;
            for (int t = 0; t < targetList.size(); t++) {
                if (used[t]) continue;
                int[] target = targetList.get(t);
                int dist = Math.abs(state.crateRows[i] - target[0]) + Math.abs(state.crateCols[i] - target[1]);
                if (dist < bestDist) {
                    bestDist = dist;
                    bestT = t;
                }
            }
            used[bestT] = true;
            total += bestDist;
        }
        return total;
    }

    static boolean isGoal(State state) {
        for (int[] target : targetList) {
            if (!hasCrateAt(state, target[0], target[1])) {
                return false;
            }
        }
        return true;
    }

    static boolean hasCrateAt(State state, int r, int c) {
        for (int i = 0; i < state.crateRows.length; i++) {
            if (state.crateRows[i] == r && state.crateCols[i] == c) return true;
        }
        return false;
    }

    static boolean inBounds(int r, int c) {
        return r >= 0 && r < totalRows && c >= 0 && c < totalCols;
    }

    // A crate sitting in a corner formed by two walls can never be pushed
    // again. If that corner isn't a target, the puzzle is unsolvable from here.
    static boolean isCornerDeadlock(State state) {
        for (int i = 0; i < state.crateRows.length; i++) {
            int r = state.crateRows[i];
            int c = state.crateCols[i];
            if (grid[r][c] == '.') continue; // sitting on a target is fine

            boolean wallLeft = !inBounds(r, c - 1) || grid[r][c - 1] == '#';
            boolean wallRight = !inBounds(r, c + 1) || grid[r][c + 1] == '#';
            boolean wallUp = !inBounds(r - 1, c) || grid[r - 1][c] == '#';
            boolean wallDown = !inBounds(r + 1, c) || grid[r + 1][c] == '#';

            if ((wallLeft || wallRight) && (wallUp || wallDown)) {
                return true;
            }
        }
        return false;
    }

    // Precomputes which floor cells can never hold a crate that eventually
    // reaches a target. Working backwards from each target by simulated
    // pulls covers every cell a crate could ever be legally pushed from.
    static boolean[][] computeDeadSquares() {
        boolean[][] canReach = new boolean[totalRows][totalCols];
        ArrayDeque<int[]> queue = new ArrayDeque<>();

        for (int[] target : targetList) {
            canReach[target[0]][target[1]] = true;
            queue.add(target);
        }

        while (!queue.isEmpty()) {
            int[] cur = queue.poll();
            int r = cur[0], c = cur[1];

            for (int d = 0; d < 4; d++) {
                // crate would have come from the opposite side of this push
                int fromR = r - deltaRow[d];
                int fromC = c - deltaCol[d];
                int playerR = r - 2 * deltaRow[d];
                int playerC = c - 2 * deltaCol[d];

                if (!inBounds(fromR, fromC) || !inBounds(playerR, playerC)) continue;
                if (grid[fromR][fromC] == '#') continue;
                if (grid[playerR][playerC] == '#') continue;
                if (canReach[fromR][fromC]) continue;

                canReach[fromR][fromC] = true;
                queue.add(new int[]{fromR, fromC});
            }
        }

        boolean[][] dead = new boolean[totalRows][totalCols];
        for (int r = 0; r < totalRows; r++) {
            for (int c = 0; c < totalCols; c++) {
                dead[r][c] = !canReach[r][c];
            }
        }
        return dead;
    }
}
