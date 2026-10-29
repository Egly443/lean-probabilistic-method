# The finite probabilistic method for graphs

[![CI](https://github.com/Egly443/lean-probabilistic-method/actions/workflows/ci.yml/badge.svg)](https://github.com/Egly443/lean-probabilistic-method/actions/workflows/ci.yml)

A Lean 4 library of the core techniques of probabilistic combinatorics, made finite so that every
probability is a finite sum and every proof is counting: the `p`-biased cube and the random graph
`G(n, p)`, the first-moment method, the union bound and the deletion method with Erdős's lower
bounds for Ramsey numbers, the Lovász Local Lemma in its general (lopsided) form, and dependent
random choice. Mathlib has the laws themselves, as measures (the product of Bernoulli
distributions `setBer(u, p)` and the binomial random graph `G(V, p)`), but none of these tools;
`MeasureBridge.lean` proves that the counting probability here agrees with them.

It is a **Mathlib-ready strawman**, written to Mathlib's conventions and offered for reuse as is,
by people and by AI systems. Anyone in the Mathlib community may upstream it, in whole or in part,
if and when they choose. The author does not plan to drive it through Mathlib review.

**Provenance:** AI-generated with human guidance. Every file:

* builds with no `sorry` and no warnings;
* uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
* passes Mathlib's `#lint`, `runLinter` and `lint-style`, and the `linter.mathlibStandardSet`
  linters;
* depends only on Mathlib;
* meets [LeanPool](https://github.com/LeanPool/lean-pool)'s content rules (file headers, no
  waivers or `set_option`).

Licensed under Apache 2.0.

## Using it

The library is pinned to Lean and Mathlib `v4.35.0-rc3` (see `lean-toolchain` and
`lakefile.toml`). To depend on it, add to your `lakefile.toml`:

```toml
[[require]]
name = "probabilistic_method"
git = "https://github.com/Egly443/lean-probabilistic-method"
rev = "main"
```

and `import ProbabilisticMethod`, or import individual modules. To build it, run
`lake exe cache get` and then `lake build`.

Releases are tagged `vX.Y.Z` from `main` by the manually triggered `Release` workflow
(`.github/workflows/release.yml`).

## Contents

| File | Main results |
|---|---|
| `ProbabilisticMethod/BernoulliWeights.lean` | The `p`-biased cube on a finite set `U`: `Finset.bernoulliWeight U p A = p ^ \|A\| (1 - p) ^ \|U \ A\|` and `Finset.bernoulliProb U p P`. The weights sum to `1` (`sum_bernoulliWeight`); `bernoulliProb_superset` (`P(F ⊆ A) = p ^ \|F\|`) and `bernoulliProb_disjoint` (`P(A ∩ F = ∅) = (1 - p) ^ \|F\|`); `Finset.DependsOnCoords` and **independence** of events on disjoint coordinate sets (`bernoulliProb_and`); **linearity of expectation** for counts (`expectation_card_filter`); **the first-moment method** (`exists_le_expectation`) and **the union bound** (`exists_forall_not_of_sum_bernoulliProb_lt`). Also `bernoulliProb_congr`, `bernoulliWeight_sdiff`, `bernoulliProb_le_one`, nonnegativity. |
| `ProbabilisticMethod/RandomGraph.lean` | `Finset.pairs s` (pairs of distinct elements; `pairs_eq_image_offDiag` identifies it with Mathlib's `s.offDiag.image Sym2.mk.uncurry`, so `card_pairs : #s.pairs = C(\|s\|, 2)` is Mathlib's `Sym2.card_image_offDiag`) and `SimpleGraph.possibleEdges V`; cliques and independent sets of `fromEdgeSet A` (`isClique_fromEdgeSet_iff`, `isClique_compl_fromEdgeSet_iff`) and their probabilities in `G(n, p)` (`bernoulliProb_isClique`, `bernoulliProb_isClique_compl`). **Biased first moment** `exists_cliqueFree_of_lt_one`: if `C(n, k) p ^ C(k, 2) + C(n, l) (1 - p) ^ C(l, 2) < 1` then `R(k, l) > n`. **Erdős** `exists_cliqueFree_of_sq_le_two_pow`: `R(k, k) > 2 ^ (k / 2)` for `k ≥ 3`. **Deletion** `exists_large_cliqueFree_of_deletion`: a set of at least `n - C(n, k) p ^ C(k, 2) - C(n, l) (1 - p) ^ C(l, 2)` vertices with no `k`-clique and no independent `l`-set. |
| `ProbabilisticMethod/LocalLemma.lean` | **The Lovász Local Lemma** (asymmetric, lopsided form) for **any finite probability**: `Finset.weightProb Ω w P = ∑ a ∈ Ω with P a, w a` for weights `w ≥ 0` of total `1` on a finite sample set, and `prod_one_sub_le_weightProb_forall_not`: under `LopsidedWeights`, `P(E i) ≤ x i ∏ j ∈ Γ i, (1 - x j)` implies that no `E i` occurs with probability at least `∏ (1 - x i)`; existence form `exists_mem_forall_not_of_weight_lll`. On the `p`-biased cube (`Ω = U.powerset`, `w = U.bernoulliWeight p`): `prod_one_sub_le_bernoulliProb_forall_not` and `exists_forall_not_of_lll` under `Lopsided`; **independence gives the hypothesis** (`lopsided_of_dependsOnCoords`, events on coordinate sets); **the symmetric Local Lemma** `exists_forall_not_of_symmetric_lll` (`e q (d + 1) ≤ 1`). Also `Avoids`, `bernoulliProb_eq_add`, `bernoulliProb_mono`. |
| `ProbabilisticMethod/DependentRandomChoice.lean` | The common-neighbour **moment identity** for any relation, `Finset.sum_card_common_eq_sum_choose` (`∑ U, #common(U) = ∑ y, C(deg y, h)`), and **moment selection** `Finset.exists_card_common_ge` (for `h ≤ \|L\|`, if `t C(\|L\|, h) ≤ ∑ y, C(deg y, h)` then some `h`-subset of `L` has `t` common neighbours). For graphs: `sum_card_commonNeighbors_tuple` (`∑ τ, #common(τ) = ∑ v, deg v ^ t`), `sum_card_bad_le`, and **dependent random choice** `exists_dependentRandomChoice` (if `a n ^ t + C(n, r) m ^ t ≤ ∑ v, deg v ^ t`, some set of `a` vertices has every `r`-subset with `m` common neighbours) with Fox and Sudakov's edge-count form `exists_dependentRandomChoice_of_card_edgeFinset`. |
| `ProbabilisticMethod/MeasureBridge.lean` | **Agreement with Mathlib's measures.** `Finset.setBernoulli_real_eq_bernoulliProb`: Mathlib's product of Bernoulli distributions `setBer(U, p)` gives a family `S` of sets the probability `U.bernoulliProb p Q` of any event `Q` agreeing with `S` on subsets of `U` (for `p : unitInterval`). `SimpleGraph.binomialRandom_real_eq_bernoulliProb`: the same for Mathlib's binomial random graph `G(V, p)` and events on sets of possible edges, with `coe_possibleEdges` (`possibleEdges V = Sym2.diagSetᶜ`). Showcase: `binomialRandom_real_isClique` (`P(s is a clique of G(V, p)) = p ^ C(\|s\|, 2)`) and `binomialRandom_real_isClique_compl`. |

The probability space is the powerset of a finite set with product weights, so nothing needs
measure theory. Independence of events on disjoint coordinate sets is proved by splitting a subset
of `U` along `T ⊆ U`, which multiplies the weights. The Local Lemma is proved by the usual strong
induction on the conditioning set, in a division-free form that never conditions on an event of
probability zero.

## Notes for anyone upstreaming to Mathlib

* **Placement.** A new `Mathlib/Combinatorics/Probabilistic/` directory: `BernoulliWeights.lean`
  as its base, `LocalLemma.lean` beside it (its finite-weights part could instead go under
  `Mathlib/Probability/`, restated for a finite measure), `DependentRandomChoice.lean` with the
  graph files, and
  `RandomGraph.lean` under `Mathlib/Combinatorics/SimpleGraph/`, and `MeasureBridge.lean` beside
  Mathlib's `Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`.
* **Lemmas that belong elsewhere.** `Finset.pairs` and `pairs_eq_image_offDiag` belong with
  `Finset.sym2` in `Mathlib/Data/Finset/Sym.lean` (Mathlib already has the cardinality as
  `Sym2.card_image_offDiag`; a reviewer may prefer `pairs` to be that image outright); `Finset.sum_card_common_eq_sum_choose` and
  `Finset.exists_card_common_ge` in `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.
* **Names.** `possibleEdges` for the pairs of distinct vertices, `Finset.pairs` for those inside a
  set. `Finset.DependsOnCoords P T` rather than `Finset.DependsOn`: Mathlib's root `DependsOn f s`
  (for functions on a pi type) would be shadowed inside `namespace Finset`; the argument order
  (event first, then coordinates) follows Mathlib's.
* **Overlap with Mathlib.** Mathlib defines the laws but not the tools. `setBernoulli`
  (`Mathlib/Probability/Distributions/SetBernoulli.lean`, notation `setBer(u, p)`) is the product
  of `p`-Bernoulli distributions on a set, and `binomialRandom`
  (`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`, notation `G(V, p)`, Yaël
  Dillies, mathlib4 PR #31364) is the binomial random graph; both carry only basic API
  (singletons, `ncard` distribution). `MeasureBridge.lean` transfers every result here to them.
  Mathlib's `Finset.sum_pow_mul_eq_add_pow` gives the total of the weights.
* **Design questions.** Weights on `U.powerset` rather than `PMF` or `Measure.pi`: the counting
  form keeps every statement elementary and decidable, and `G(n, p)` is just `U = possibleEdges V`.
  This follows advice on the Lean Zulip (Bhavik Mehta and Kevin Buzzard, *new members*, "Diagonal
  Ramsey Number Lower Bound", 2020) that cardinality arguments are the easiest way to formalise the
  probabilistic method; Yaël Dillies noted (*Formal conjectures*, "Erdős 625: random graphs",
  2025) that the open question is how best to represent Bernoulli random variables so that
  binomial random graphs are painless. Mathlib chose `setBer`; a reviewer may prefer the tools
  stated for `setBer(U, p)` directly, with this file's counting as the proof method and
  `MeasureBridge.lean` as the translation. The
  Local Lemma is stated for the lopsided hypothesis, which contains the standard dependency-graph
  version (`lopsided_of_dependsOnCoords`) and the Erdős–Spencer lopsided version.
* **Older Mathlib.** `Finset.prod_le_one` was renamed (`prod_le_one₀`) and
  `Finset.prod_le_prod_of_subset` added in `v4.35`; the file proves the small product lemma it
  needs privately. `Mathlib.Data.Real.Basic` is deprecated in `v4.35`; reals come through
  `Mathlib.Tactic.Rify`.

## Relation to other libraries

[lean-ramsey](https://github.com/Egly443/lean-ramsey) proves Erdős's diagonal lower bound by a
direct count of colourings; here it is one instance of the biased first-moment bound, alongside
the off-diagonal and deletion forms. [LeanPool](https://github.com/LeanPool/lean-pool) and TauCeti have no Local Lemma, `G(n, p)` or
dependent random choice.

Earlier formalisations discussed on the Lean Zulip, none in Mathlib: Nathan Glover's asymmetric and
symmetric Lovász Local Lemma for a general probability measure, in Lean 4
(`nsglover/Lean-4.0-LLL` at `f2eb7cd`, toolchain `v4.4.0-rc1`, `LLL/Main.lean`:
`lovasz_local_lemma`, `symmetric_lovasz_local_lemma`), ported from his Lean 3 original
(`nsglover/lean-lovasz-local-lemma` at `c10a8b2`) and announced on Zulip (*general*, "Lovasz
Local Lemma - mathlib4 Contribution", December 2023), with Yves Jäckle's version in his master's
thesis code; Bhavik Mehta's Lean 3 count proof of Erdős's lower
bound (`b-mehta/combinatorics`, branch `graphs` at `d3f649b`, `src/lower_ramsey.lean`); Yaël Dillies's extremal probabilistic
combinatorics in LeanCamCombi (`LeanCamCombi/ExtrProbCombi`). Mehta's measure-theoretic
independence of `Measure.pi` on disjoint coordinate sets (*Is there code for X?*, "finite product
measure on disjoint restrictions", 2025) is the measure form of `bernoulliProb_and`. Nothing here is
derived from any of them.

## Not included

* The Local Lemma lower bound `R(k, k) > (√2 / e) k 2 ^ (k / 2) (1 - o(1))`: the finite statement
  needs the count of `k`-sets meeting a given one in an edge; left for a follow-up.
* The second-moment method (Chebyshev, Paley–Zygmund) and thresholds in `G(n, p)`: Mathlib's
  measure-theoretic variance would be the natural home, through a bridge to `Measure.pi`.

## Citation

The mathematics is from the works below. BibTeX entries for Mathlib's `docs/references.bib` are in
`references.bib`, each checked against zbMATH and normalised with the `bibtool` command from
Mathlib's `scripts/lint-bib.sh`.

* P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947), 292–294,
  doi:10.1090/S0002-9904-1947-08785-1.
* P. Erdős, L. Lovász, *Problems and results on 3-chromatic hypergraphs and some related
  questions*, in *Infinite and finite sets* (Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10
  (1975), 609–627.
* P. Erdős, J. Spencer, *Lopsided Lovász local lemma and Latin transversals*, Discrete Appl. Math.
  30 (1991), 151–154, doi:10.1016/0166-218X(91)90040-4.
* J. Fox, B. Sudakov, *Dependent random choice*, Random Structures Algorithms 38 (2011), 68–99,
  doi:10.1002/rsa.20344.
* N. Alon, J. H. Spencer, *The probabilistic method*, 4th ed., Wiley, 2016.
