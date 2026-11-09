#!/usr/bin/env python3
"""Independent finite checks for revision 4.

Standard library only, Python >= 3.10. These checks test the mathematical
representation, not ontology or Gödel's general theorems. No Coq is called.
"""
from __future__ import annotations
import itertools
import json
import time
from pathlib import Path


def posets(n: int):
    """All labelled partial orders: 3 choices per unordered pair, then transitivity."""
    pairs = list(itertools.combinations(range(n), 2))
    for choices in itertools.product(range(3), repeat=len(pairs)):
        up = [1 << i for i in range(n)]
        for (i, j), choice in zip(pairs, choices):
            if choice == 1:
                up[i] |= 1 << j
            elif choice == 2:
                up[j] |= 1 << i
        valid = True
        for i in range(n):
            for j in range(n):
                if up[i] >> j & 1 and up[j] & ~up[i]:
                    valid = False
                    break
            if not valid:
                break
        if valid:
            yield tuple(up)


def upsets(up: tuple[int, ...]) -> list[int]:
    n = len(up)
    return [m for m in range(1 << n)
            if all(not (m >> i & 1) or not (up[i] & ~m) for i in range(n))]


def implication(up: tuple[int, ...], a: int, b: int) -> int:
    bad = a & ~b
    return sum(1 << i for i, future in enumerate(up) if not (future & bad))


def directed(up: tuple[int, ...], i: int) -> bool:
    cone = [j for j in range(len(up)) if up[i] >> j & 1]
    return all(up[u] & up[v] for u in cone for v in cone)


def linearly_ordered(up: tuple[int, ...], i: int) -> bool:
    cone = [j for j in range(len(up)) if up[i] >> j & 1]
    return all((up[u] >> v & 1) or (up[v] >> u & 1) for u in cone for v in cone)


def ideals(up: tuple[int, ...]) -> list[int]:
    n = len(up)
    return [m for m in range(1 << n)
            if all(not (m >> j & 1) or all(not (up[i] >> j & 1) or (m >> i & 1)
                                         for i in range(n)) for j in range(n))]


def ideal_frame(items: list[int]) -> tuple[int, ...]:
    return tuple(sum(1 << j for j, d in enumerate(items) if not (c & ~d)) for c in items)


def main() -> None:
    start = time.perf_counter()
    by_size: dict[str, int] = {}
    unary = binary = residuation = 0
    frame_laws = 0
    # All labelled posets up to size 5; all valuations for the listed properties.
    for n in range(1, 6):
        count = 0
        full = (1 << n) - 1
        for up in posets(n):
            count += 1
            values = upsets(up)
            neg = {a: implication(up, a, 0) for a in values}
            imp = {(a, b): implication(up, a, b) for a in values for b in values}
            wem_all = lem_all = dne_all = dummett_all = full
            for a in values:
                unary += 1
                na, nna = neg[a], neg[neg[a]]
                assert a & na == 0
                assert implication(up, a & na, 0) == full
                assert a & ~nna == 0
                assert neg[neg[neg[a]]] == na
                wem_all &= na | nna
                lem_all &= a | na
                dne_all &= imp[nna, a]
                for b in values:
                    binary += 1
                    r = imp[a, b]
                    assert r in neg, 'Implication must be upward closed'
                    assert not (r & a & ~b)
                    assert imp[a, a] == full
                    assert imp[a, imp[b, a]] == full
                    assert imp[a & b, a] == full
                    assert imp[a, a | b] == full
                    assert imp[a & imp[a, b], b] == full
                    assert imp[imp[a, b], imp[neg[b], neg[a]]] == full
                    assert imp[a & neg[a], b] == full
                    assert neg[neg[a] & neg[b]] == neg[neg[a | b]]
                    dummett_all &= r | imp[b, a]
                    # Independent construction as union of all stable compatible conditions.
                    union = 0
                    for z in values:
                        residuation += 1
                        lhs = not (z & a & ~b)
                        rhs = not (z & ~r)
                        assert lhs == rhs, 'Residuation mismatch'
                        assert imp[imp[a, b] & imp[b, z], imp[a, z]] == full
                        assert imp[imp[a, z] & imp[b, z], imp[a | b, z]] == full
                        if lhs:
                            union |= z
                    assert union == r
            for i in range(n):
                frame_laws += 4
                assert bool(wem_all >> i & 1) == bool(directed(up, i))
                assert bool(dummett_all >> i & 1) == bool(linearly_ordered(up, i))
                terminal = up[i] == 1 << i
                assert bool(lem_all >> i & 1) == terminal
                assert bool(dne_all >> i & 1) == terminal
        by_size[str(n)] = count
    assert by_size == {'1': 1, '2': 3, '3': 19, '4': 219, '5': 4231}

    ideal_count = projections = expressive_values = topology_pairs = 0
    for n in range(1, 5):
        for event_up in posets(n):
            cuts = ideals(event_up)
            up = ideal_frame(cuts)
            values = upsets(up)
            full = (1 << len(cuts)) - 1
            atoms = [sum(1 << i for i, c in enumerate(cuts) if c >> d & 1)
                     for d in range(n)]
            ideal_count += 1
            for a in values:
                expressive_values += 1
                expressed = 0
                for i, c in enumerate(cuts):
                    if a >> i & 1:
                        conjunct = full
                        for d in range(n):
                            if c >> d & 1:
                                conjunct &= atoms[d]
                        expressed |= conjunct
                assert expressed == a
                na = implication(up, a, 0)
                cl = sum(1 << i for i, future in enumerate(up) if future & a)
                boundary = cl & ~a & full
                assert boundary == (full & ~(a | na))
                for b in values:
                    topology_pairs += 1
                    pointwise = (full & ~a) | b
                    interior = sum(1 << i for i, future in enumerate(up)
                                   if not (future & ~pointwise))
                    assert interior == implication(up, a, b)
            # Check the projection/back property for every nonempty subsystem-chain.
            for s in range(1, 1 << n):
                events = [d for d in range(n) if s >> d & 1]
                if not all((event_up[d] >> e & 1) or (event_up[e] >> d & 1)
                           for d in events for e in events):
                    continue
                projections += 1
                local = sorted(set(c & s for c in cuts))
                for c in cuts:
                    for j in local:
                        if (c & s) & ~j:
                            continue
                        down_j = sum(1 << d for d in range(n)
                                     if event_up[d] & j)
                        u = c | down_j
                        assert u in cuts and not (c & ~u) and (u & s) == j

    # Named witnesses used in the text (descriptive models, not physical histories).
    chain = (0b11, 0b10)
    p, top = 0b10, 0b11
    np = implication(chain, p, 0)
    assert not ((p | np) & 1)
    imp_only = implication(chain, implication(chain, p, top),
                           implication(chain, implication(chain, np, top), top))
    assert imp_only == top
    diamond = ideal_frame([0, 1, 2, 3])
    d, e = 0b1010, 0b1100
    assert not ((implication(diamond, d, e) | implication(diamond, e, d)) & 1)
    assert implication(diamond, d, 0) | implication(diamond, implication(diamond, d, 0), 0) == 15
    # Constant atom valuations on a nontrivial chain remain Boolean under all operations.
    assert all(implication(chain, a, b) in {0, 3} for a in {0, 3} for b in {0, 3})

    result = {
        'status': 'PASS',
        'scope': 'finite descriptive frames only; no ontological or Gödel completeness claim',
        'labelled_posets_by_size': by_size,
        'labelled_posets_total': sum(by_size.values()),
        'unary_valuations': unary,
        'binary_valuations': binary,
        'residuation_triples': residuation,
        'pointwise_frame_equivalence_checks': frame_laws,
        'ideal_lattices_sizes_1_to_4': ideal_count,
        'local_chain_projections': projections,
        'expressive_upsets': expressive_values,
        'topological_implication_pairs': topology_pairs,
        'named_counterexamples': {
            'fixed_C_not_equivalent_to_disjunction': True,
            'two_linearizations_not_two_ontological_histories': 'representation only',
            'constant_language_can_be_classical_before_terminal': True
        },
        'elapsed_seconds': round(time.perf_counter() - start, 6),
        'coq_or_vm_executed': False
    }
    target = Path(__file__).with_name('verification_results.json')
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
