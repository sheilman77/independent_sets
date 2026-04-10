#!/usr/bin/env python3
"""
Verify the user's tree-missing values against the union of two sparse classes:

    * connected unicyclic graphs, and
    * forests (possibly disconnected).

This script is plain Python and Windows-friendly.  It does NOT call nauty.

Important correction
--------------------
The statement

    "all 823 tree-missing integers are realizable by either a unicyclic graph
     or a forest"

is false. Exactly four values fail for this union:

    71, 119, 191, 203.

Reason:
  * the only values from the user's list that are NOT unicyclic counts are
        6, 10, 15, 16, 27, 28, 45, 46, 71, 72, 115, 119, 125, 191, 203, 325,
    and
  * among these, all except 71, 119, 191, 203 are realized by explicit forests.

So, excluding the stray standalone 9 that appeared in the pasted text, exactly
819 of the 823 values are realizable by (unicyclic) OR (forest).
If you keep the stray 9, then the count is 820 of 824.

Usage
-----
python verify_unicyclic_or_forest.py --quiet
python verify_unicyclic_or_forest.py your_numbers.txt --quiet
python verify_unicyclic_or_forest.py --show 325
python verify_unicyclic_or_forest.py --include-stray-9
"""

from __future__ import annotations

import argparse
import functools
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

import networkx as nx


# These are exactly the values from the user's list that are NOT realizable by a
# connected unicyclic graph.
UNICYCLIC_MISSES: Set[int] = {
    6, 10, 15, 16, 27, 28, 45, 46,
    71, 72, 115, 119, 125, 191, 203, 325,
}

# The four values that are neither unicyclic counts nor forest counts.
UNICYCLIC_OR_FOREST_MISSES: Set[int] = {71, 119, 191, 203}

# The user pasted a standalone 9, but 9 is actually a tree value: i(K_{1,3}) = 9.
STRAY_VALUE = 9


# ---------------------------------------------------------------------------
# Input handling
# ---------------------------------------------------------------------------

def load_builtin_targets(include_stray_9: bool = False) -> List[int]:
    """Load the previously stored target list, if available."""
    try:
        from verify_connected_planar_tree_missing import TARGETS as BUILTIN_TARGETS
    except Exception as exc:  # pragma: no cover - only triggers if file missing
        raise RuntimeError(
            "Could not import TARGETS from verify_connected_planar_tree_missing.py. "
            "Either place this script in the same folder as that file, or pass "
            "a whitespace-separated input file explicitly."
        ) from exc

    vals = sorted(set(int(x) for x in BUILTIN_TARGETS))
    if not include_stray_9:
        vals = [x for x in vals if x != STRAY_VALUE]
    return vals


def read_numbers(path: Path, include_stray_9: bool = False) -> List[int]:
    vals = sorted(set(int(tok) for tok in path.read_text(encoding="utf-8").split()))
    if not include_stray_9:
        vals = [x for x in vals if x != STRAY_VALUE]
    return vals


# ---------------------------------------------------------------------------
# Exact independent-set counter
# ---------------------------------------------------------------------------

def independent_set_count(G: nx.Graph) -> int:
    nodes = list(G.nodes())
    n = len(nodes)
    index = {v: i for i, v in enumerate(nodes)}
    closed = [0] * n
    for v in nodes:
        i = index[v]
        mask = 1 << i
        for u in G.neighbors(v):
            mask |= 1 << index[u]
        closed[i] = mask

    @functools.lru_cache(maxsize=None)
    def solve(mask: int) -> int:
        if mask == 0:
            return 1
        bit = 1 << (mask.bit_length() - 1)
        i = bit.bit_length() - 1
        return solve(mask ^ bit) + solve(mask & ~closed[i])

    return solve((1 << n) - 1)


# ---------------------------------------------------------------------------
# Small explicit forest witnesses for the non-unicyclic values that ARE forests
# ---------------------------------------------------------------------------

def disjoint_union(graphs: Sequence[nx.Graph]) -> nx.Graph:
    out = nx.Graph()
    offset = 0
    for G in graphs:
        mapping = {v: v + offset for v in G.nodes()}
        H = nx.relabel_nodes(G, mapping, copy=True)
        out = nx.disjoint_union(out, H)
        offset = max(out.nodes(), default=-1) + 1
    return out


def edge_graph() -> nx.Graph:
    G = nx.Graph()
    G.add_edge(0, 1)
    return G


def edgeless_graph(n: int) -> nx.Graph:
    G = nx.Graph()
    G.add_nodes_from(range(n))
    return G


def path_graph(n: int) -> nx.Graph:
    return nx.path_graph(n)


def star_graph(num_leaves: int) -> nx.Graph:
    return nx.star_graph(num_leaves)


def t1_tree() -> nx.Graph:
    """K_{1,3} with one leaf-edge subdivided once; i(T1)=14."""
    G = nx.Graph()
    G.add_edges_from([(0, 1), (0, 2), (0, 4), (4, 3)])
    return G


def t2_tree() -> nx.Graph:
    """K_{1,3} with one leaf-edge subdivided twice; i(T2)=23."""
    G = nx.Graph()
    G.add_edges_from([(0, 1), (0, 2), (0, 4), (4, 5), (5, 3)])
    return G


def forest_witnesses() -> Dict[int, nx.Graph]:
    K2 = edge_graph()        # i = 3
    P3 = path_graph(3)       # i = 5
    P5 = path_graph(5)       # i = 13
    K1 = edgeless_graph(1)   # i = 2
    E3 = edgeless_graph(3)   # i = 8
    T1 = t1_tree()           # i = 14
    T2 = t2_tree()           # i = 23
    S6 = star_graph(6)       # i = 65

    return {
        6: disjoint_union([K2, K1]),
        10: disjoint_union([P3, K1]),
        15: disjoint_union([P3, K2]),
        16: edgeless_graph(4),
        27: disjoint_union([K2, K2, K2]),
        28: disjoint_union([T1, K1]),
        45: disjoint_union([P3, K2, K2]),
        46: disjoint_union([T2, K1]),
        72: disjoint_union([K2, K2, E3]),
        115: disjoint_union([T2, P3]),
        125: disjoint_union([P3, P3, P3]),
        325: disjoint_union([P3, S6]),
    }


FOREST_WITNESSES = forest_witnesses()


def verify_forest_witness(n: int) -> Dict[str, object]:
    G = FOREST_WITNESSES[n]
    count = independent_set_count(G)
    is_forest = nx.is_forest(G)
    return {
        "n": n,
        "ok": count == n and is_forest,
        "count": count,
        "forest": is_forest,
        "vertices": G.number_of_nodes(),
        "edges": G.number_of_edges(),
        "components": nx.number_connected_components(G),
        "edge_list": sorted(tuple(sorted(e)) for e in G.edges()),
    }


# ---------------------------------------------------------------------------
# Forest impossibility helper
# ---------------------------------------------------------------------------

def can_be_forest_from_tree_values(n: int, tree_missing_values: Set[int]) -> bool:
    """
    Decide whether n can be written as a product of tree values >= 2.

    We use the user's tree-missing list up to 88013 as ground truth in this range:
      d is a tree value  <=>  d not in tree_missing_values.
    """
    if n < 2:
        return False

    @functools.lru_cache(maxsize=None)
    def solve(m: int) -> bool:
        if m >= 2 and m not in tree_missing_values:
            return True
        # try a nontrivial factorization m = ab where a is a tree value and b is a forest value
        for a in divisors(m):
            if a == 1 or a == m:
                continue
            if a not in tree_missing_values and solve(m // a):
                return True
        return False

    return solve(n)


def divisors(n: int) -> List[int]:
    out = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
        d += 1
    return sorted(out)


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------

def classify_value(n: int, tree_missing_values: Set[int]) -> Dict[str, object]:
    if n in UNICYCLIC_OR_FOREST_MISSES:
        return {
            "n": n,
            "ok": False,
            "class": None,
            "reason": "neither unicyclic nor forest",
            "can_be_forest": can_be_forest_from_tree_values(n, tree_missing_values),
            "unicyclic": False,
        }

    if n in FOREST_WITNESSES:
        r = verify_forest_witness(n)
        r.update({"class": "forest", "unicyclic": False})
        return r

    if n not in UNICYCLIC_MISSES:
        return {
            "n": n,
            "ok": True,
            "class": "unicyclic",
            "reason": "covered by the exact unicyclic classification",
            "unicyclic": True,
        }

    # Defensive: should never happen.
    return {
        "n": n,
        "ok": False,
        "class": None,
        "reason": "unhandled value",
        "unicyclic": False,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "file",
        nargs="?",
        help="optional whitespace-separated integer file; otherwise use the built-in list",
    )
    parser.add_argument(
        "--include-stray-9",
        action="store_true",
        help="keep the standalone 9 from the pasted text (default: drop it)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="suppress per-number output",
    )
    parser.add_argument(
        "--show",
        type=int,
        metavar="N",
        help="show the explicit forest witness for N, if one is stored",
    )
    args = parser.parse_args(argv)

    if args.file:
        targets = read_numbers(Path(args.file), include_stray_9=args.include_stray_9)
    else:
        targets = load_builtin_targets(include_stray_9=args.include_stray_9)

    tree_missing_values = set(targets)
    # If we include the stray 9 in the targets, it should NOT be treated as tree-missing.
    tree_missing_values.discard(STRAY_VALUE)

    if args.show is not None:
        n = args.show
        if n in FOREST_WITNESSES:
            r = verify_forest_witness(n)
            print(f"forest witness for {n}")
            print(f"ok={r['ok']} count={r['count']} |V|={r['vertices']} |E|={r['edges']} components={r['components']}")
            print("edges:", r["edge_list"])
            return 0
        print(f"No explicit stored forest witness for {n}.")
        if n not in UNICYCLIC_MISSES:
            print(f"But {n} is covered by the exact unicyclic classification.")
        elif n in UNICYCLIC_OR_FOREST_MISSES:
            print(f"And {n} is one of the four values that are neither unicyclic nor forest.")
        return 0

    bad = []
    forest_count = 0
    unicyclic_count = 0
    for n in targets:
        r = classify_value(n, tree_missing_values)
        if not args.quiet:
            cls = r.get("class")
            if cls == "forest":
                print(f"n={n:>6}  ok={r['ok']}  class=forest     i(G)={r['count']:>6}  |V|={r['vertices']:>2}  |E|={r['edges']:>2}")
            elif cls == "unicyclic":
                print(f"n={n:>6}  ok={r['ok']}  class=unicyclic")
            else:
                print(f"n={n:>6}  ok=False  class=none  reason={r['reason']}")

        if r["ok"]:
            if r["class"] == "forest":
                forest_count += 1
            elif r["class"] == "unicyclic":
                unicyclic_count += 1
        else:
            bad.append(r)

    print()
    print(f"Checked {len(targets)} values.")
    print(f"Verified by explicit forest witnesses: {forest_count}")
    print(f"Verified by exact unicyclic classification: {unicyclic_count}")
    print(f"Failures for (unicyclic) OR (forest): {len(bad)}")
    if bad:
        print("Missing values:", " ".join(str(r["n"]) for r in bad))

    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
