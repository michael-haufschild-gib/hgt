import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsAPhasedSumOverHeckePoints

/-!
# The constant term of the Hecke trace at a primary prime

For the projected theta function `θ_s` (Fourier series `Σ_h b(v, h) e(ξ_hz)`), the Hecke points of
`(z, v)` are `(pz, |p|v)` and `((z + 3t)/p, v/|p|)`. Three tools compute the constant term of the Hecke trace:

* averaging over `O/p` (`sum_cuspCharacterSeries_low`):
  `Σ_{x ∈ O/p} S_c((z + 3x)/p) = N(p) S_{c(·p)}(z)`, since `x ↦ e(ξ_k·3x/p)` is the principal trace character of
  `O/p` at `k` (`tracePhase_low`), primitive, so its sum is `N(p)` or `0` as `p ∣ k` or not;
* products of cusp series are cusp series of the convolution (`cuspCharacterSeries_mul`);
* cross-Parseval for the dilate `S_a(pz)` (`integral_cuspCharacterSeries_mul_dilate`).

With `β_y` from the Bezout matrices (`pδ_y − 9yβ_y = 1`) the result is (`integral_sourceHeckeTrace`)

`∫_P Tr_pθ_s = N(p)|P| (2 Σ_h b(|p|v, h) b(v/|p|, −p²h) + Σ_{y≢0} (3y/p)₃ Σ_k b(v/|p|, k) e(−ξ_k·3β_y/p) b(v/|p|, −k))`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

/-! ### Products of cusp series -/

/-- The convolution `(c ⋆ d)(m) = Σ_k c(k) d(m − k)`. -/
def cuspConv (c d : O → ℂ) (m : O) : ℂ := ∑' k : O, c k * d (m - k)

/-- `(m, k) ↦ (k, m − k)`. -/
def convEquiv : O × O ≃ O × O where
  toFun q := (q.2, q.1 - q.2)
  invFun r := (r.1 + r.2, r.1)
  left_inv q := by simp
  right_inv r := by simp

theorem summable_conv_family {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖)) :
    Summable (fun q : O × O => ‖c q.2‖ * ‖d (q.1 - q.2)‖) := by
  have h := hc.mul_norm hd
  simp only [norm_mul] at h
  exact (convEquiv.summable_iff (f := fun r : O × O => ‖c r.1‖ * ‖d r.2‖)).mpr h

theorem summable_cuspConv {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖)) :
    Summable (fun m => ‖cuspConv c d m‖) := by
  have hF := summable_conv_family hc hd
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hF.prod
  have hs : Summable (fun k => ‖c k * d (m - k)‖) := by
    simpa only [norm_mul] using hF.prod_factor m
  calc ‖cuspConv c d m‖ ≤ ∑' k, ‖c k * d (m - k)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' k, ‖c k‖ * ‖d (m - k)‖ := by simp only [norm_mul]

theorem cuspFrequency_add_sub (k m : O) : cuspFrequency k + cuspFrequency (m - k) = cuspFrequency m := by
  simp only [cuspFrequency, map_sub]
  ring

/-- **Products of cusp series.** `S_c S_d = S_{c ⋆ d}`. -/
theorem cuspCharacterSeries_mul {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (u : ℂ) : cuspCharacterSeries c u * cuspCharacterSeries d u = cuspCharacterSeries (cuspConv c d) u := by
  have hcs : Summable (fun k => ‖c k * tracePhase (cuspFrequency k * u)‖) := by
    simpa only [norm_mul, tracePhase_norm, mul_one] using hc
  have hds : Summable (fun k => ‖d k * tracePhase (cuspFrequency k * u)‖) := by
    simpa only [norm_mul, tracePhase_norm, mul_one] using hd
  have hF := summable_conv_family hc hd
  set G : O × O → ℂ := fun q => c q.2 * d (q.1 - q.2) * tracePhase (cuspFrequency q.1 * u) with hG
  have hGs : Summable G := by
    refine Summable.of_norm_bounded hF fun q => ?_
    simp only [hG, norm_mul, tracePhase_norm, mul_one, le_refl]
  unfold cuspCharacterSeries
  rw [tsum_mul_tsum_of_summable_norm hcs hds,
    ← convEquiv.tsum_eq (fun r : O × O => c r.1 * tracePhase (cuspFrequency r.1 * u) *
      (d r.2 * tracePhase (cuspFrequency r.2 * u)))]
  have hterm : ∀ q : O × O, c (convEquiv q).1 * tracePhase (cuspFrequency (convEquiv q).1 * u) *
      (d (convEquiv q).2 * tracePhase (cuspFrequency (convEquiv q).2 * u)) = G q := by
    intro q
    simp only [convEquiv, Equiv.coe_fn_mk, hG]
    rw [show c q.2 * tracePhase (cuspFrequency q.2 * u) * (d (q.1 - q.2) *
        tracePhase (cuspFrequency (q.1 - q.2) * u)) =
        c q.2 * d (q.1 - q.2) * (tracePhase (cuspFrequency q.2 * u) *
          tracePhase (cuspFrequency (q.1 - q.2) * u)) by ring, ← AddChar.map_add_eq_mul, ← add_mul,
      cuspFrequency_add_sub]
  simp_rw [hterm]
  rw [hGs.tsum_prod]
  refine tsum_congr fun m => ?_
  simp only [hG, cuspConv]
  rw [tsum_mul_right]

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Averaging over `O/p` -/

/-- `e(ξ_k·3x/p) = ψ_p(xk)`, the principal trace character modulo `p`. -/
theorem tracePhase_low (k x : O) :
    tracePhase (cuspFrequency k * (3 * ringComplex x / ringComplex P.p)) =
      principalTraceChar P.p P.ne_zero (P.res x * P.res k) := by
  have hP := P.ringComplex_ne_zero
  have hτ : ringComplex traceLambda ≠ 0 :=
    MetaplecticMobiusDescent.CubicEisenstein.ringComplex_ne_zero traceLambda_ne_zero
  rw [← map_mul, ← tracePhase_div_eq_principalTraceChar P.p (x * k) P.ne_zero]
  congr 1
  simp only [cuspFrequency, map_mul]
  field_simp

theorem sum_tracePhase_low (k : O) :
    ∑ x : P.Res, tracePhase (cuspFrequency k * (3 * ringComplex (P.lift x) / ringComplex P.p)) =
      if P.p ∣ k then (Fintype.card P.Res : ℂ) else 0 := by
  simp_rw [P.tracePhase_low, res_lift]
  rw [AddChar.sum_mulShift _ (principalTraceChar_primitive P.p P.ne_zero)]
  by_cases hk : P.p ∣ k
  · rw [if_pos ((P.res_eq_zero_iff k).mpr hk), if_pos hk]
  · rw [if_neg (fun h => hk ((P.res_eq_zero_iff k).mp h)), if_neg hk]
    simp

/-- **Averaging over `O/p`.** `Σ_x S_c((z + 3x)/p) = N(p) S_{c(·p)}(z)`. -/
theorem sum_cuspCharacterSeries_low (c : O → ℂ) (hc : Summable (fun h => ‖c h‖)) (z : ℂ) :
    ∑ x : P.Res, cuspCharacterSeries c ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) =
      (Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => c (m * P.p)) z := by
  have hP := P.ringComplex_ne_zero
  have hsum : ∀ x : P.Res, Summable (fun k => c k *
      tracePhase (cuspFrequency k * ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p))) := fun x =>
    Summable.of_norm (by simpa only [norm_mul, tracePhase_norm, mul_one] using hc)
  unfold cuspCharacterSeries
  rw [← Summable.tsum_finsetSum (fun x _ => hsum x)]
  have hpt : ∀ k, ∑ x : P.Res, c k *
      tracePhase (cuspFrequency k * ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p)) =
      c k * tracePhase (cuspFrequency k * (z / ringComplex P.p)) *
        (if P.p ∣ k then (Fintype.card P.Res : ℂ) else 0) := by
    intro k
    rw [← P.sum_tracePhase_low k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_div, mul_add, AddChar.map_add_eq_mul]
    ring
  simp_rw [hpt]
  have hinj : Function.Injective (fun m : O => m * P.p) := fun a b h => mul_right_cancel₀ P.ne_zero h
  have hsupp : Function.support (fun k => c k * tracePhase (cuspFrequency k * (z / ringComplex P.p)) *
      (if P.p ∣ k then (Fintype.card P.Res : ℂ) else 0)) ⊆ Set.range (fun m : O => m * P.p) := by
    intro k hk
    by_contra hn
    apply hk
    have hk' : ¬ P.p ∣ k := fun ⟨m, hm⟩ => hn ⟨m, by rw [hm, mul_comm]⟩
    simp only [if_neg hk', mul_zero]
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [if_pos (dvd_mul_left _ _), cuspFrequency_mul_right,
    show cuspFrequency m * ringComplex P.p * (z / ringComplex P.p) = cuspFrequency m * z by field_simp]
  ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
