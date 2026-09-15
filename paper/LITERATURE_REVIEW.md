# Literature review for the universal carry-collapse theorem

## Scope

This review supports the manuscript **Conservation of Quantitative Information under Change of Representation** after the universal carry-collapse theorem replaced the earlier operational capstone as the repository's main result.

The question is now:

> Which established theories already contain pieces of the residual/carry projective structure, and which of them prove that this structure is forced for an arbitrary optimal lossless finite code with no positional syntax assumed?

The review is deliberately scoped. It is not an exhaustive historical priority search.

The closest neighboring areas are:

1. numeration systems and finite automata;
2. abstract and generalized numeration systems;
3. canonical number systems;
4. odometers / adding machines and inverse limits of cyclic factors;
5. carry propagation of successor;
6. information-lossless finite-state coding;
7. periodic enumeration and structural derivations of positional equations.

The comparison criterion is not whether the literature contains carry, successor, cyclic dynamics, or modulo projections. It does. The criterion is **what structure is assumed before those objects appear, and whether arbitrary optimal lossless recodings are proved rigid up to conjugacy and projective equivalence**.

---

## 1. Numeration systems and finite automata

Frougny and collaborators developed a substantial theory of number representation, normalization, and arithmetic by finite automata and transducers. Representative sources include Frougny (1992), Frougny (1999), and the Frougny–Sakarovitch survey chapter (2010).

These works study arithmetic once a numeration architecture is already specified: an integer or non-integer base, a recurrence, a digit language, or a normalization relation.

### Relation to the present theorem

The overlap is real: finite-state representation, normalization, successor, and carry-like mechanisms all occur in this literature.

The logical direction differs. The universal carry-collapse theorem starts with an arbitrary finite code type `Code` carrying no numeral syntax and assumes only:

- an injective encoding of the complete finite quantity window `Fin (b^k)`;
- a state budget `|Code| ≤ b^k`.

Cardinality forces the encoding to be bijective, and exact successor is then unique up to conjugacy. No digit language is required.

So this literature is a close downstream neighbor, not a duplicate theorem.

---

## 2. Abstract numeration systems

Abstract numeration systems represent integers through words of an ordered language rather than through powers of a fixed radix. Lecomte–Rigo and Rigo survey a broad family of such systems.

The framework is more general than ordinary radix notation, but the representation language and its order are part of the input.

### Relation to the present theorem

The universal carry-collapse theorem does not assume a language, lexicographic order, digit alphabet, or native representation of successor on words. The code can be an arbitrary finite type.

Therefore the theorem is not a statement that all abstract numeration systems reduce syntactically to a fixed radix. Rather, it says that **when a complete finite quantitative window is encoded losslessly at optimal state count, the resulting finite successor dynamics is conjugate to the canonical cycle and its coherent depth reductions are forced residual maps**.

This is an invariant statement about exact finite quantitative compression, not a classification of all numeration languages.

---

## 3. Canonical number systems and generalized radix representations

Canonical number systems and generalized radix systems study when a given algebraic base/digit architecture yields finite or unique representations. Representative sources include Akiyama–Pethő (2002) and the Akiyama–Borbély–Brunotte–Pethő–Thuswaldner survey (2004).

### Relation to the present theorem

These theories typically begin with a radix-like object and digit set and ask whether representations are finite, canonical, or unique.

The present universal theorem asks a different rigidity question. At a fixed finite depth, once the complete quantity window has exactly enough code capacity and no information loss, **any** code is a bijective coordinate system on the same finite quantitative state space. The theorem then determines the exact successor and cross-depth factor maps independently of how the code is spelled.

The result therefore concerns invariance under representation change rather than canonicality of a prescribed algebraic base.

---

## 4. Odometers, adding machines, and inverse limits

Odometers are one of the closest mathematical neighbors of the final theorem. Grabner, Liardet, and Tichy (1995) study odometers associated with systems of numeration. Barat, Berthé, Liardet, and Thuswaldner (2006) survey dynamical approaches to numeration.

In the standard dynamical formulation, an odometer is built from finite cyclic factors whose connecting maps are residual reductions. For a constant capacity `b`, the familiar finite factors are cyclic systems of sizes

$$
b,
\quad b^2,
\quad b^3,
\quad \ldots
$$

with successor given by addition of one and factor maps given by reduction modulo lower powers.

### Relation to the present theorem

The repository's final projective object is precisely of this familiar odometer type after canonical coordinates are chosen:

$$
\operatorname{Fin}(b^m)
\longrightarrow
\operatorname{Fin}(b^k),
\qquad
n\longmapsto n\bmod b^k.
$$

The distinction is the direction of the theorem.

Classical odometer constructions **define** or study the inverse/projective system of cyclic factors. The universal carry-collapse theorem starts instead with arbitrary opaque finite code spaces at every depth. It proves that:

- every code level is forced to be bijective with the canonical finite cycle;
- every exact successor is forced to be the conjugated cyclic successor;
- every zero-preserving successor-equivariant map between ordered depths is uniquely the conjugated residual map;
- the identity and composition laws therefore follow for the arbitrary code tower.

Thus the theorem may be read as a **rigidity/recognition theorem for the finite projective odometer structure under optimal lossless quantitative coding**.

The manuscript should not claim to discover odometers or inverse limits. The contribution is that this structure is forced from arbitrary optimal lossless finite representations, and the claim is machine-checked in Lean 4.

---

## 5. Carry propagation of successor

Berthé, Frougny, Rigo, and Sakarovitch (2020) study carry propagation for the successor function across several kinds of numeration systems: ordinary, abstract, rational-base, greedy, and beta systems.

Their starting point is an existing numeration system with representations of integers. Carry propagation measures how representation digits change under `N → N+1`.

### Relation to the present theorem

The repository proves an upstream invariance result. In the canonical finite window,

$$
S_k(n)=0
\iff
n+1\equiv 0\pmod{b^k},
$$

and `carry-geometry` identifies the right-hand side with `carryAfterIncrementAtDepth b k n`.

Because every optimal lossless code is conjugate to the canonical finite window and every exact successor is unique, the wrap/carry event is invariant under arbitrary coordinate recoding.

So carry-propagation theory asks what carry does inside given systems; the present theorem proves that the finite wrap event corresponding to carry cannot be removed by optimal lossless recoding.

---

## 6. Information-lossless finite-state coding

Dai, Lathrop, Lutz, and Mayordomo (2004) characterize finite-state dimension through compression ratios achieved by information-lossless finite-state compressors. The shared theme is preservation of recoverable information under finite-state coding.

### Relation to the present theorem

The present finite-window hypothesis is simpler and more rigid: the encoder itself is injective on a complete finite quantitative window, and the code has no more states than the number of distinct quantities being encoded.

This immediately forces exact cardinality and bijectivity.

Finite-state dimension studies asymptotic compressibility of sequences; it does not, in the cited work, derive the residual/carry projective hierarchy. The useful conceptual connection is the invariance of distinguishability under lossless coding.

The manuscript should therefore use information-lossless coding as conceptual context, not as a claim that the same theorem is already standard in compression theory.

---

## 7. Periodic enumeration and positional equations

Manca (2024), *The Archimedean Origin of Modern Positional Number Systems*, is an important structural precedent. It derives a base-representation recurrence from an Archimedean monotone enumeration system with a period.

This is genuinely close because positional equations are obtained from periodic organization rather than merely postulated.

### Relation to the present theorem

Manca's framework already contains:

- strings over a finite symbol set;
- a monotone enumeration;
- a period;
- an append operation on numeral strings.

The universal carry-collapse theorem does not start from a numeral language at all. Its main route is a finite rigidity theorem for arbitrary code spaces. The earlier constructive branch of this repository separately derives a local capacity before constructing cycle coordinates and canonical digits.

Manca therefore remains an important comparison, but the new universal theorem is best distinguished by **representation opacity and conjugacy/projective rigidity**, not by claiming that positional structure has never been derived from periodicity before.

---

## 8. Comparison matrix

| Literature | Structure assumed at input | Typical object/result | Difference from universal carry-collapse theorem |
|---|---|---|---|
| Frougny / automata | numeration system, base/recurrence, digit language | normalization and arithmetic transducers | code syntax/numeration architecture already specified |
| Abstract numeration systems | ordered language over finite alphabet | integer representations and recognizability | representation language is primitive |
| Canonical number systems | algebraic base + digit set | finite/unique expansions | radix architecture is primitive |
| Odometers | cyclic factors and connecting maps / numeration scale | adding-machine dynamics, inverse limits | projective cyclic structure is constructed/assumed rather than forced from opaque codes |
| Carry propagation | established numeration representations | statistics/dynamics of digit changes under successor | carry exists before analysis |
| Information-lossless finite-state coding | finite-state compressor + recoverability | compression ratios / finite-state dimension | different target; no forced residual tower |
| Manca 2024 | periodic monotone enumeration of numeral strings | base recurrence and positional equation | period and numeral language already explicit |
| This repository | injective encoding of complete `b^k` window into arbitrary finite code with `|Code|≤b^k`, at all depths | forced bijection, unique successor, carry wrap, unique residual projections, projective equivalence | syntax-free rigidity theorem up to change of representation |

---

## 9. The strongest defensible novelty statement

The literature surveyed here already contains all of the following ingredients in other contexts:

- finite-state and automata models of numeration;
- successor dynamics and carry propagation;
- odometers / adding machines;
- inverse limits of finite cyclic systems with residual maps;
- information-lossless coding;
- structural derivations of positional equations from periodic systems.

The manuscript should therefore avoid claims such as “carry has never been derived before” or “odometer structure is new.”

A stronger and more precise statement is:

> **The contribution is a representation-rigidity theorem. For every finite depth, an arbitrary opaque optimal lossless encoding of the complete `b^k` quantitative window is forced to be a bijective coordinate change of the canonical cyclic successor system. Across depths, every zero-preserving successor-equivariant map is uniquely the conjugated residual projection, so the entire code tower is projectively equivalent to the canonical residual/carry tower.**

Within the scoped review, we did not find this exact implication stated with the same primitive data and the same conclusion.

That is a scoped literature observation, not an exhaustive historical priority claim.

---

## 10. Recommended paper positioning

A publication-facing introduction can state the relation to prior work as follows:

> Numeration theory, automata theory, carry propagation, and odometer dynamics provide rich analyses of representations once a numeration architecture or cyclic factor system has been specified. Information-lossless finite-state coding provides a separate language for exact recoverability under finite-state constraints. The present result addresses a rigidity question at the intersection of these themes. At every depth `k`, we allow a completely opaque finite code for the full set of `b^k` quantitative states and assume only injectivity together with the optimal state budget. This forces bijectivity. Exact unit successor is then unique up to conjugacy, its wrap event is the carry-through-depth event, and zero-preserving successor-equivariant maps between depths are uniquely residual reductions after decoding and re-encoding. Consequently the full arbitrary code tower is projectively equivalent to the canonical residual/carry tower. The theorem does not propose a new odometer construction; it proves that optimal lossless finite quantitative recodings cannot escape that projective dynamics.

---

## 11. Role of the earlier constructive branch

The earlier modules in the repository remain important but should no longer carry the main novelty claim of the paper.

They prove a complementary non-circular construction:

```text
finite-state obstruction
→ information escape
→ unbounded distinguishing depth
→ explicit unit dynamics
→ local recurrence
→ emergent capacity
→ cycle coordinates
→ quotient/remainder crosswalk
→ carry normalization
→ finite positional expansion
→ intrinsic digit uniqueness
```

This route explains how positional coordinates can emerge under explicit operational assumptions.

The universal carry-collapse branch instead proves that once complete finite quantitative windows are represented optimally and without loss, arbitrary coordinate syntax cannot produce a different exact quantitative dynamics or hierarchy.

The paper can present the universal theorem first and the emergent construction as a complementary structural explanation.

---

## 12. Core references retained for the manuscript

The existing `references.bib` already contains the principal sources needed for the rewritten paper:

- Frougny (1992, 1999);
- Frougny–Sakarovitch (2010);
- Lecomte–Rigo (2010);
- Rigo (2014);
- Grabner–Liardet–Tichy (1995);
- Barat–Berthé–Liardet–Thuswaldner (2006);
- Akiyama–Pethő (2002);
- Akiyama et al. (2004);
- Berthé–Frougny–Rigo–Sakarovitch (2020);
- Heuberger–Kropf–Prodinger (2017);
- Dai–Lathrop–Lutz–Mayordomo (2004);
- Manca (2024).

For a later journal-specific revision, citation chaining should focus especially on odometer recognition/conjugacy results and on finite-state lossless coding, since those are now closer to the final theorem than the earlier canonical-number-system comparison.