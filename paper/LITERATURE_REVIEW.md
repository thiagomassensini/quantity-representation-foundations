# Literature review for the foundational capstone

## Scope of this review

This document is a scoped literature review for the manuscript **Conservation of Quantitative Information under Change of Representation**. Its purpose is not to claim an exhaustive priority search. It asks a narrower question:

> Which established research programs come closest to the formal implication proved in this repository, and where does the logical direction differ?

The comparison is organized around six neighboring literatures:

1. number representation and finite automata;
2. abstract numeration systems;
3. canonical number systems and generalized radix representations;
4. odometers and dynamical systems associated with numeration;
5. carry propagation and successor dynamics;
6. information-lossless finite-state coding;
7. period/enumeration principles that lead to positional equations.

The central comparison criterion is **what the prior work assumes before positional structure appears**.

---

## 1. Number representation and finite automata

A major body of work initiated and developed by Christiane Frougny and collaborators studies normalization, arithmetic, and recognizability in already specified numeration systems. Frougny's 1992 paper studies numeration systems defined by linear recurrences and asks when normalization and addition can be realized by finite automata. Later surveys by Frougny and Sakarovitch place integer-base, real-base, canonical, rational-base, and automata/transducer viewpoints in a common framework.

Representative references:

- Frougny (1992), *Representations of Numbers and Finite Automata*.
- Frougny (1999), *On-line Finite Automata for Addition in Some Numeration Systems*.
- Frougny and Sakarovitch (2010), *Number Representation and Finite Automata*.

### Relation to the present project

The overlap is substantial at the level of mechanisms: finite-state dynamics, normalization, addition, and carry-like transport are central in both settings.

The logical starting point is different. This literature normally begins with a numeration architecture: a base or recurrence, an alphabet of digits, a language of representations, or a normalization problem. The present capstone instead begins with an abstract quantity type `Q`, an injective unit-step trajectory, a globally faithful split representation, and finite autonomous local dynamics. The radix-like capacity is not part of the primitive representation.

Therefore this literature is best described as **downstream-neighboring** rather than as a duplicate of the capstone theorem.

---

## 2. Abstract numeration systems

Abstract numeration systems replace ordinary positional powers by representations given by words in an ordered language, often a regular language. The framework is particularly close conceptually because it separates the set of integers from a specific integer base and studies representations via formal languages and automata.

Representative references:

- Lecomte and Rigo (2010), *Abstract Numeration Systems*.
- Rigo (2014), *A Range of Numeration Systems*.
- Rigo (2001) and related work on regular-language numeration systems.

A characteristic feature is that the representation language is part of the system. Integers are mapped to words, commonly by genealogic or lexicographic ordering, and questions of recognizability, arithmetic, and automaticity are then studied.

### Relation to the present project

Abstract numeration systems are broader than ordinary fixed-radix notation, but they still assume a representation language over a finite alphabet. By contrast, the foundational capstone does not begin with a word language, digit alphabet, lexicographic order, or representation map `N -> words`. It derives a finite cycle capacity first and then constructs the digit list recursively.

The most important contrast is:

- **ANS direction:** choose or define a language of representations, then study the induced numeration system;
- **capstone direction:** impose faithful finite-local operational dynamics, derive a capacity and unique cycle/residual coordinates, then obtain a canonical positional language.

The present theorem should therefore not be advertised as a replacement for abstract numeration systems. It is an upstream characterization result under a more specialized dynamic hypothesis.

---

## 3. Canonical number systems and generalized radix representations

Canonical number systems (CNS) and related generalized radix systems study finite expansions in algebraic settings, frequently with a polynomial or algebraic base and a prescribed digit set. The characteristic questions are existence, uniqueness, finiteness of expansions, and structural criteria on the base.

Representative references:

- Akiyama and Pethő (2002), *On Canonical Number Systems*.
- Akiyama, Borbély, Brunotte, Pethő, and Thuswaldner (2004), *On a Generalization of the Radix Representation -- A Survey*.

### Relation to the present project

The present manuscript eventually reaches a statement resembling the canonicality property: every external clock value has a unique finite expansion with bounded digits and no leading zero. However, CNS theory normally starts with a base/digit pair or polynomial and asks whether it has the finiteness/canonicality property.

The capstone reverses this direction in its restricted operational setting. The finite capacity `b` is obtained as the unique least positive local return and only afterwards acts as the radix in the derived expansion.

This distinction should be explicit in any novelty statement:

> The contribution is not a new criterion for a pre-existing number system to be canonical; it is a theorem that a canonical fixed-capacity positional system appears from an explicit finite-local dynamic representation model.

---

## 4. Numeration dynamics and odometers

There is a long-established dynamical viewpoint on numeration. Grabner, Liardet, and Tichy introduced `G`-odometers associated with `G`-scale expansions. Barat, Berthé, Liardet, and Thuswaldner later surveyed numeration from a dynamical viewpoint, including beta-numeration, abstract systems, shift radix systems, `G`-scales, and odometers.

Representative references:

- Grabner, Liardet, and Tichy (1995), *Odometers and Systems of Numeration*.
- Barat, Berthé, Liardet, and Thuswaldner (2006), *Dynamical Directions in Numeration*.

These works are particularly relevant because the successor operation acts dynamically on digit expansions, and odometers are canonical models of repeated addition with carry propagation.

### Relation to the present project

This is one of the closest conceptual neighborhoods, but the direction is again reversed.

The `G`-odometer literature starts from a scale `G=(G_n)` and the corresponding expansion, then studies the dynamical system naturally associated with incrementing represented integers.

The capstone starts from unit-step dynamics on an abstract state space and finite autonomous local observation. It proves that the least positive local return is a unique capacity `b>1`, constructs cycle coordinates without division/modulo, and only then identifies the successor boundary event as carry.

A concise comparison is:

> odometer theory: numeration -> successor dynamics;
>
> foundational capstone: constrained successor dynamics -> positional numeration.

This reversal is likely one of the manuscript's most defensible conceptual contributions.

---

## 5. Carry propagation

Carry is itself a mature research subject. Frougny studied on-line finite automata for addition in nonstandard numeration systems. Heuberger, Kropf, and Prodinger studied the statistics of carries in signed-digit representations. Berthé, Frougny, Rigo, and Sakarovitch studied amortized carry propagation for the successor function across several classes of numeration systems.

Representative references:

- Frougny (1999), *On-line Finite Automata for Addition in Some Numeration Systems*.
- Heuberger, Kropf, and Prodinger (2017), *Analysis of Carries in Signed Digit Expansions*.
- Berthé, Frougny, Rigo, and Sakarovitch (2020), *The Carry Propagation of the Successor Function*.

### Relation to the present project

The 2020 successor paper is especially close in vocabulary: it studies how many digits change when passing from the representation of `N` to that of `N+1`. But a numeration system and its representations already exist before carry propagation is measured.

The capstone isolates an earlier question:

> Why should the local successor dynamics acquire a carry boundary at all?

Within the explicit operational assumptions, the answer is that finite autonomous injective local dynamics yields a least positive return. Relative to that return, the recursive coordinates have only two successor regimes: advance inside the cycle, or reset the residual and increment the completed-cycle count. The latter is then identified with the usual carry normalization.

Thus the paper should cite carry-propagation work as a direct downstream neighbor and state that it addresses **the emergence of the carry boundary**, not the asymptotic statistics of propagation after a numeration system is fixed.

---

## 6. Information-lossless finite-state coding

Information theory and finite-state compression contain a closely related notion of faithfulness: an information-lossless finite-state compressor is required to preserve enough output/final-state information to reconstruct its input. Finite-state dimension characterizes compression ratios attainable by such information-lossless devices.

Representative reference:

- Dai, Lathrop, Lutz, and Mayordomo (2004), *Finite-State Dimension*.

### Relation to the present project

The shared invariant is injectivity/recoverability. The present `FaithfulRepresentation` is intentionally even more primitive: it is simply injectivity of an encoding. The finite-state obstruction then says that an infinite source cannot inject into a finite state space.

However, finite-state compression theory does not, in the cited work, derive a positional numeral system from losslessness. Its goal is compression complexity of sequences. Therefore this literature supports the terminology of information preservation but should not be presented as a source of the positional conclusion.

A safe formulation is:

> The project uses a notion of faithfulness structurally analogous to information-losslessness, but asks a different question: what representational architecture is forced when a finite local state must participate in an unbounded, nonrepeating, information-preserving unit trajectory?

---

## 7. Periodic enumeration as a route to positional equations

Vincenzo Manca's 2024 paper *The Archimedean Origin of Modern Positional Number Systems* is an important close comparison. It studies monotone enumeration systems based on orders and periods and proves a base-representation recurrence of the form

`value(alpha x) = value(alpha) p + value(x)`,

from which the usual positional expansion follows by iteration.

### Why this is genuinely close

Both projects emphasize that periodic/cyclic structure can explain positional weighting rather than simply taking a positional formula as primitive.

### Why the theorem is not the same

Manca's Archimedean monotone enumeration system already assumes:

- numerals as strings over a finite symbol set;
- a period `p`;
- an append-a-digit operation;
- a monotone enumeration/order condition connecting strings to represented integers.

The present capstone assumes none of those as primitive. Its local capacity `b` is derived as a least positive return in finite autonomous injective local dynamics; the digit/residual coordinate is constructed afterwards; and the positional list is obtained by iterating the emergent quotient.

Accordingly, Manca should be presented not as something to dismiss but as **the closest known structural precedent found in this scoped review for deriving a positional equation from periodic organization**. The manuscript's distinct step is moving the period itself downstream, deriving it from finite-local operational dynamics.

---

## 8. Comparison matrix

| Literature | Primitive structure already assumed | Typical conclusion | Relation to the capstone |
|---|---|---|---|
| Frougny / automata | base or recurrence, digits/representations | normalization/addition computable by automata | downstream neighbor |
| Abstract numeration systems | ordered language over finite alphabet | representation/recognizability/automaticity | broader representation language, but language assumed |
| Canonical number systems | algebraic/polynomial base + digit set | finite/unique expansions | canonicality after base is given |
| Odometers | `G`-scale and expansion | successor dynamics / dynamical properties | opposite logical direction |
| Carry propagation | established numeration system | statistics/algorithms of carry propagation | studies carry after it exists |
| Information-lossless finite-state coding | finite-state transducer + recoverability | compression/dimension | shares faithfulness, different target |
| Manca 2024 | strings, finite symbols, monotone period `p` | base recurrence and positional formula | closest structural precedent; period assumed |
| This repository | abstract `Q`, injective unit trajectory, faithful split representation, finite autonomous injective local dynamics, first-step nontriviality | unique `b>1`, QR-like cycle coordinates, carry boundary, finite canonical positional expansion | derives capacity before digits/base |

---

## 9. What the literature supports us saying

A defensible manuscript-level positioning is:

> Classical and generalized numeration theory develops a rich theory of representations once a base, scale, digit set, representation language, or numeration system has been specified. Dynamical approaches attach odometers and successor maps to such systems; automata theory studies normalization and arithmetic; and carry-propagation theory studies the dynamics and statistics of carries. The present work reverses a portion of this logical direction in a restricted, explicit operational model. Starting from a faithful nonrepeating unit-step trajectory with finite autonomous injective local observation and a nontrivial first local step, it derives a unique local capacity, constructs bounded cycle coordinates without primitive division or modulo, identifies the boundary transition as carry, and obtains an intrinsically unique finite positional representation of the external step clock.

This formulation is strong but bounded.

---

## 10. What the literature does not justify us saying

The scoped review does **not** justify any of the following unconditional priority claims:

- "This is the first derivation of positional notation from first principles."
- "No previous work derives positional systems from periodicity or dynamics."
- "All faithful representations must be positional."
- "Finite-state information conservation universally implies quotient--remainder."
- "The capstone subsumes abstract numeration systems, canonical number systems, or odometer theory."

Manca (2024) alone makes the second sentence untenable, and the breadth of generalized numeration theory makes broad universal claims inappropriate without a much more exhaustive historical review.

The safest novelty statement is conditional and structural:

> **In the literature examined here, we did not find the same implication with the same primitive data: an abstract source trajectory and finite autonomous information-preserving local dynamics from which the radix-like capacity itself is derived before quotient, remainder, digits, or carry are introduced.**

That is evidence from a scoped review, not a claim of exhaustive priority.

---

## 11. Recommended related-work paragraph for the paper

A publication version can use language close to the following:

> Our result sits at the intersection of several established theories of numeration. Finite automata and transducers have long been used to study normalization and arithmetic in integer, beta, linear-recurrence, and related numeration systems; abstract numeration systems replace a fixed radix by ordered languages; canonical number-system theory studies existence and uniqueness of finite expansions for prescribed algebraic bases and digit sets; and odometer constructions encode the successor dynamics associated with given expansions. Carry propagation has also been studied directly, including for nonstandard and abstract systems. These theories predominantly take a numeration architecture---a base, scale, digit set, representation language, or expansion---as part of the input. A particularly close structural precedent is Manca's derivation of a base-representation recurrence from a monotone periodic enumeration system. The present theorem moves one step upstream in a different direction: within an explicit operational model, the local period/capacity is itself derived from finite autonomous injective dynamics before quotient, remainder, digits, or carry are introduced. The resulting positional representation is then identified downstream with the standard one.

---

## 12. References selected for the manuscript

The accompanying `references.bib` contains the core references used in this review. The list is intentionally compact enough for a first paper draft. A later submission pass should expand it through citation-chaining from the most relevant surveys, especially Barat--Berthé--Liardet--Thuswaldner, Frougny--Sakarovitch, Lecomte--Rigo, and Akiyama et al.
