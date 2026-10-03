# mordell-five

A Lean formalization of the five-point Mordell inequality, including its equality case.

五阶 Mordell 不等式及完整等号条件的 Lean 形式化。

For any five complex numbers with `∑ i, Complex.normSq (z i) = 5`,

```text
∏ i < j, Complex.normSq (z i - z j) ≤ 3125,
```

with equality exactly for a unit regular pentagon centered at the origin, up to a common rotation and arbitrary relabeling. No centering, distinctness, or symmetry assumption is imposed on the input.

The main theorem is in [Mordell/Original.lean](Mordell/Original.lean):

```lean
theorem Mordell.original : Mordell.OriginalStatement
```

## Build

Lean **4.30.0** and the mathlib revision pinned in `lake-manifest.json` are required. With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

To inspect the theorem and its axioms:

```lean
import Mordell
#check Mordell.original
#print axioms Mordell.original
```

The proof uses only `propext`, `Classical.choice`, and `Quot.sound`. It contains no `sorry`, added axioms, or `native_decide`. The proof source was independently rebuilt and its exact root and transitive assumptions checked before upload.

## Proof

Compactness and genuine stationarity reduce the problem to global maximizers. Exact resultant identities and ideal-membership proofs split all coefficient cases. Rational interval certificates bound every real root in the two generic quartic branches. All non-pentagonal branches lie strictly below 3125, completing the maximum classification and both directions of the equality characterization.

The algebraic route draws on Jie Wang, *The Five-Point Case of Mordell’s Discriminant Inequality*, [arXiv:2610.00358v1](https://arxiv.org/abs/2610.00358). All required identities and certificates are proved within Lean; no external symbolic computation is trusted.

This repository contains only the main proof, its local import dependencies, and build configuration. Research drafts, logs, verification dumps, generated binaries, and local caches are omitted.
