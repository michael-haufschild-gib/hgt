# Almost all zeros of cos(hD)Ξ are real, for every h > 0

- **ID:** cosine-family-almost-all-real
- **Stage:** 5-failed (DUPLICATE of formalized corpus results)
- **Type:** THEOREM (paper), Lean in progress
- **Source:** route-candidates loop row 722 (claim `4N(½+h,T) + O(log T)`); Opus loop row 979
- **Statement:** For `0 < h < ½` let `A_h(z) = (Ξ(z+ih) + Ξ(z−ih))/2`. For every `ε > 0`, in the Littlewood windows `[T₁, T₂] ⊂ [U/4, U/2]` of `ZetaFixedSigmaDensity`, for all large `U`, the non-real zeros of `A_h` with `Re z ∈ [T₁, T₂]` have total multiplicity `≤ ε (T₂ − T₁) log U`.

## Goal
An unconditional density-one statement for the cosine family. At `h ≥ ½` every zero is real (corpus `laguerrePolya_cosineShiftXi`). Under RH every zero is real for each `h > 0`. This card shows that the defect is negligible for each fixed `h > 0`, with no hypothesis. The LP defect of `cos(hD)Ξ` is controlled only by the zeros of `ξ` to the right of `½ + h`, which have density zero (Bohr–Landau / Selberg).

## Gates
- [x] 0 → 1  in-progress: statement fixed, every ingredient located in the corpus
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach (paper proof)
1. **Defect disks** (corpus `cosineShift_nonreal_zero_mem_defectDisk`). Every non-real zero `z` of `A_h` has a zero `w` of `Ξ` with `(Re w − Re z)² + (Im z)² + h² ≤ (Im w)²`. Hence `|Im w| > h` and `|z − Re w| < ½`.
2. **Local count for `A_h`** (new). Let `a_h(s) = (ξ(s−h) + ξ(s+h))/2`, so `A_h(z) = a_h(½ + iz)`.
   - On `Re s = σ₀` (`σ₀` large) the ratio `r = ξ(s−h)/ξ(s+h)` has `|r| ≤ e^{−2hB} ≤ ½`, using `Re ξ'/ξ ≥ B` on the far right half-plane (`exists_re_logDeriv_xi_ge_halfPlane`).
   - Hence `|a_h'/a_h| ≤ 2|ξ'/ξ(s+h)| + |ξ'/ξ(s−h)| ≤ C + 3 log(|t| + C)` (`norm_logDeriv_xi_le_of_two_le_re`).
   - By the even order-one Hadamard factorization of `A_h`, the partial fraction of `a_h'/a_h` over its zeros, paired by the reflection `s ↦ 1 − s`, gives a Lorentzian mass bound: `#{zeros of a_h with |γ − t| ≤ 1} ≤ C(1 + log(|t| + 3))`.
3. **Count.** Every non-real zero of `A_h` with `Re z ∈ [T₁, T₂]` lies within `½` of `Re w` for a zero `ρ` of `ξ` with `|Re ρ − ½| > h` and `Im ρ ∈ [T₁ − ½, T₂ + ½]`.
   - By symmetry the number of such `ρ` is at most `2 #{β ≥ ½ + h}`, which is `≤ ε'(T₂ − T₁)` (`eventually_zeroCount_fixedSigma_le`).
   - Each contributes `≤ C log U` zeros of `A_h` (step 2), so the total is `≤ 2ε'C (T₂ − T₁) log U`.

## Log
- 2026-10-12 — created at stage 1. All ingredients except step 2 are in the corpus (`XiCosineShiftDefectDisks`, `ZetaFixedSigmaDensity`, `LorentzianZeroMass`, `XiLogDerivFarRight`, `OrderOneHadamardFactorization`).
- 2026-10-12 — **retired as duplicate.** The corpus already proves stronger statements:
  `XiCosineShiftNonrealZeroCount.exists_card_cosineShift_nonrealZeros_le` (power-saving count
  `D(1+log T)^{B+1} T^{(A(½+h)+ε)(½−h)}` via Ingham–Huxley, with the same local `O(log x)` count from
  the log-derivative at `x − i(3/2+h)`), `XiCosineShiftDefectTransportAllHeights.eventually_windowDefectCount_le_transport`
  (sharp `2·#{deep ρ} + 2`), and `XiCosineShiftAlmostEveryHeight` (full-density real-rootedness in
  heights). The step-2 module drafted here (horizontal-growth proof of the local count) was deleted.
  Positive survivor: none needed; the statement is owned. Lesson: run
  `research "cosine shift nonreal zero count"` before drafting.
