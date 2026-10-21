import GaloisForLFunctions.ArithmeticIncidencePositivity.SharedStripSurplusAllocation

/-!
# The light cone of the shared surplus: all thin prime strips at every scale

For an odd test supported in `[−r, r]`, `N = e^{2r}`, call the integers `n` with
`2r − 2δ ≤ log n < 2r` the light-cone band of width `δ` (`lightConeBand`): their strips
`S_n = [log n − r, r]` all lie in `[r − 2δ, r]` and are thinner than `δ`. The band holds about
`2δN` integers, each atom `Λ(n)/√n ≤ 2r/(e^r(1 − δ))`, so its total mass is at most
`(2δe^{2r} + 1) · 4r/(e^r (1 − δ))`. For `δ ≤ e^{−r}/(16r)` and `r ≥ 2` this is below `1.6`, under the
sharp micro-fold constant `1.89` of such thin strips, and the union allocation pays every atom of the
band at once (`sum_primeShift_le_lightCone`):

    Σ_{2r − 2δ ≤ log n < 2r} 2 Λ(n)/√n ∫ F(x) F(x + log n) dx ≤ T(r − 2δ, r).

The band holds `≍ e^r/r` integers, so the number of atoms paid simultaneously grows without bound.

**Why this is the scale.** The surplus is a logarithmic energy: a bump of width `ε` at the common
edge `r` costs `≍ ε log(η/ε)`, while every strip wider than `ε` charges `½ ∫ f²` to its odd part.
The surplus pays a nested family of odd parts only while the atom mass per width layer stays bounded;
the mass of the layer `[η, 2η]` is `≍ η e^r`. Hence `η ≲ e^{−r}`: the band of integers
`N − c√N < n < N`, the square-root scale of `N`. The factor `1/r` here comes from the trivial count of
the band; a Brun–Titchmarsh bound removes it.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The light-cone band at radius `r` of width `δ`: the integers `n` with `2r − 2δ ≤ log n < 2r`. -/
def lightConeBand (r δ : ℝ) : Finset ℕ :=
  (Finset.range ⌈Real.exp (2 * r)⌉₊).filter fun n => 2 * r - 2 * δ ≤ Real.log n ∧ Real.log n < 2 * r

/-- A member of the band satisfies `e^{2r} e^{−2δ} ≤ n` and `n ≥ 2`. -/
theorem le_of_mem_lightConeBand {r δ : ℝ} (hrδ : δ < r) {n : ℕ} (hn : n ∈ lightConeBand r δ) :
    Real.exp (2 * r - 2 * δ) ≤ n ∧ 2 ≤ n ∧ 2 * r - 2 * δ ≤ Real.log n ∧ Real.log n < 2 * r := by
  simp only [lightConeBand, Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨-, h1, h2⟩ := hn
  have hpos : 0 < Real.log n := by linarith
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact_mod_cast h
  refine ⟨?_, ?_, h1, h2⟩
  · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr h1
  · by_contra h
    have h1' : n ≤ 1 := by omega
    have : Real.log n ≤ 0 := by
      apply Real.log_nonpos hn0.le; exact_mod_cast h1'
    linarith

/-- The band holds at most `2δ e^{2r} + 1` integers. -/
theorem card_lightConeBand_le {r δ : ℝ} (hrδ : δ < r) (hδ : 0 ≤ δ) :
    ((lightConeBand r δ).card : ℝ) ≤ 2 * δ * Real.exp (2 * r) + 1 := by
  set A := Real.exp (2 * r - 2 * δ) with hA
  set B := Real.exp (2 * r) with hB
  have hsub : lightConeBand r δ ⊆ Finset.Ico ⌈A⌉₊ ⌈B⌉₊ := fun n hn => by
    have h := le_of_mem_lightConeBand hrδ hn
    simp only [lightConeBand, Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr h.1, hn.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  -- `B − A = e^{2r}(1 − e^{−2δ}) ≤ 2δ e^{2r}`
  have hBA : B - A ≤ 2 * δ * B := by
    have e : A = B * Real.exp (-(2 * δ)) := by
      rw [hA, hB, ← Real.exp_add]; ring_nf
    have := Real.add_one_le_exp (-(2 * δ))
    rw [e]; nlinarith
  have hcB : (⌈B⌉₊ : ℝ) < B + 1 := Nat.ceil_lt_add_one hB0
  have hcA : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  calc ((lightConeBand r δ).card : ℝ) ≤ ((⌈B⌉₊ - ⌈A⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * δ * B + 1 := by
      rcases le_total ⌈A⌉₊ ⌈B⌉₊ with h | h
      · rw [Nat.cast_sub h]; linarith
      · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; positivity

/-- On the band every atom is at most `2r/(e^r (1 − δ))`. -/
theorem vonMangoldtAtom_le_of_mem_lightConeBand {r δ : ℝ} (hrδ : δ < r) (hδ1 : δ < 1) {n : ℕ}
    (hn : n ∈ lightConeBand r δ) :
    vonMangoldtAtom n ≤ 2 * r / (Real.exp r * (1 - δ)) := by
  obtain ⟨hA, h2, -, hlog⟩ := le_of_mem_lightConeBand hrδ hn
  have hE := Real.exp_pos r
  -- `√n ≥ e^{r − δ} ≥ e^r (1 − δ)`
  have hsq : Real.exp (r - δ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (Real.exp_pos _).le (Nat.cast_nonneg n), ← Real.exp_nat_mul]
    convert hA using 2; push_cast; ring
  have hlow : Real.exp r * (1 - δ) ≤ Real.exp (r - δ) := by
    have e : Real.exp (r - δ) = Real.exp r * Real.exp (-δ) := by rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-δ)]) hE.le
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  unfold vonMangoldtAtom
  rw [if_pos h2]
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 2 * r :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlog.le
  have h1δ : 0 < 1 - δ := by linarith
  rw [div_le_div_iff₀ hs0 (by positivity)]
  have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith [mul_le_mul hΛ (hlow.trans hsq) (by positivity) (by linarith)]

/-- **The mass of the light cone.** For `r ≥ 2` and `0 < δ ≤ e^{−r}/(16r)`:
`Σ_{band} 2Λ(n)/√n ≤ 1.6`. -/
theorem sum_vonMangoldtAtom_lightConeBand_le {r δ : ℝ} (hr : 2 ≤ r) (hδ0 : 0 < δ)
    (hδ : δ ≤ Real.exp (-r) / (16 * r)) :
    ∑ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤ 16 / 10 := by
  set E := Real.exp r with hEdef
  have hE0 : 0 < E := Real.exp_pos r
  have he := Real.exp_one_gt_d9
  -- `e^r ≥ e² (r − 1) ≥ e² r/2`
  have hE2 : Real.exp 1 ^ 2 * (r - 1) ≤ E := by
    have h := Real.add_one_le_exp (r - 2)
    have e : E = Real.exp 1 ^ 2 * Real.exp (r - 2) := by
      rw [hEdef, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have he2 : 7389 / 1000 ≤ Real.exp 1 ^ 2 := by nlinarith
  have hrE : 4 * r ≤ 1083 / 1000 * E := by nlinarith
  have hEinv : Real.exp (-r) = 1 / E := by rw [Real.exp_neg, hEdef, one_div]
  rw [hEinv] at hδ
  have hδE : 16 * r * E * δ ≤ 1 := by
    rw [le_div_iff₀ (by positivity), le_div_iff₀ hE0] at hδ
    linarith
  have hδs : δ ≤ 1 / 200 := by
    have : 16 * 2 * 7 ≤ 16 * r * E := by nlinarith
    nlinarith
  have hrδ : δ < r := by linarith
  -- each atom and the count
  have hcard := card_lightConeBand_le hrδ hδ0.le
  have hexp2 : Real.exp (2 * r) = E ^ 2 := by
    rw [hEdef, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [hexp2] at hcard
  have hterm : ∀ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤ 2 * (2 * r / (E * (1 - δ))) :=
    fun n hn => by linarith [vonMangoldtAtom_le_of_mem_lightConeBand hrδ (by linarith) hn]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hq0 : 0 ≤ 2 * (2 * r / (E * (1 - δ))) := by
    have : 0 < 1 - δ := by linarith
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcard hq0
  -- `(2δE² + 1) · 4r/(E(1 − δ)) ≤ (1/2 + 1.083)/(1 − δ) ≤ 1.6`
  have hfin : (2 * δ * E ^ 2 + 1) * (2 * (2 * r / (E * (1 - δ)))) ≤ 16 / 10 := by
    have h1δ : 0 < 1 - δ := by linarith
    rw [show (2 * δ * E ^ 2 + 1) * (2 * (2 * r / (E * (1 - δ)))) =
      (8 * δ * r * E + 4 * r / E) / (1 - δ) by field_simp; ring]
    rw [div_le_iff₀ h1δ]
    have h4 : 4 * r / E ≤ 1083 / 1000 := by rw [div_le_iff₀ hE0]; linarith
    nlinarith
  linarith

section LightCone

variable {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0)

include hF hFc hodd hFL hsupp in
/-- **The light cone of the shared surplus.** For every `r ≥ 2`, `0 < δ ≤ e^{−r}/(16r)` and every odd
`F` supported in `[−r, r]`, all the atoms of the band `2r − 2δ ≤ log n < 2r` are paid at once by one
copy of the surplus of `[r − 2δ, r]`:
`Σ_{band} 2Λ(n)/√n ∫ F(x) F(x + log n) dx ≤ T(r − 2δ, r)`. -/
theorem sum_primeShift_le_lightCone {δ : ℝ} (hr : 2 ≤ r) (hδ0 : 0 < δ)
    (hδ : δ ≤ Real.exp (-r) / (16 * r)) :
    ∑ n ∈ lightConeBand r δ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
      stripBoxEnergy F (r - 2 * δ) r := by
  have hmass := sum_vonMangoldtAtom_lightConeBand_le hr hδ0 hδ
  -- `δ ≤ e^{−2}/32 ≤ 1/200`
  have hE : Real.exp (-r) ≤ 1 / 7 := by
    have he := Real.exp_one_gt_d9
    have h2 : Real.exp 2 ≤ Real.exp r := Real.exp_le_exp.mpr hr
    have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos r) (by norm_num)]
    nlinarith
  have hδs : δ ≤ 1 / 200 := by
    calc δ ≤ Real.exp (-r) / (16 * r) := hδ
      _ ≤ (1 / 7) / (16 * 2) := div_le_div₀ (by norm_num) hE (by norm_num) (by linarith)
      _ ≤ 1 / 200 := by norm_num
  have hrδ : δ < r := by linarith
  -- weights `θ_n = 2Λ(n)/√n / 1.89`
  set θ : ℕ → ℝ := fun n => 2 * vonMangoldtAtom n / (189 / 100) with hθdef
  have hθsum : ∑ n ∈ lightConeBand r δ, θ n ≤ 1 := by
    rw [hθdef, ← Finset.sum_div, div_le_one (by norm_num)]
    linarith
  have h := sum_primeStripCharge_le_union hF hFc hodd hFL hsupp (lightConeBand r δ)
    (p₀ := r - 2 * δ) (by linarith) (by linarith) (by linarith) θ (fun _ => 0) fun n hn => by
      obtain ⟨-, h2, hlo, hhi⟩ := le_of_mem_lightConeBand hrδ hn
      have hΛ0 := vonMangoldtAtom_nonneg n
      refine ⟨h2, ⟨by linarith, by linarith⟩, by linarith, by positivity, by norm_num, ?_⟩
      -- the strip constant is at least `1.89`
      have hlam : 189 / 100 ≤ stripFoldConstant n r := by
        unfold stripFoldConstant
        have hp : 19 / 10 ≤ Real.log n - r := by linarith
        have hη0 : 0 ≤ (r - (Real.log n - r)) / 2 := by linarith
        have hη : (r - (Real.log n - r)) / 2 ≤ 1 / 200 := by linarith
        have hηp : (r - (Real.log n - r)) / 2 / (Real.log n - r) ≤ 1 / 300 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have hη2 : 3 * ((r - (Real.log n - r)) / 2) ^ 2 ≤ 3 / 40000 := by nlinarith
        linarith
      rw [hθdef]
      simp only
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      nlinarith
  have h' := h hθsum
  simp only [primeStripCharge, mul_zero, zero_mul, add_zero] at h'
  exact h'

end LightCone

/-- **The light cone for `C¹` tests.** For every odd `C¹` test supported in `[−r, r]`, `r ≥ 2`,
`0 < δ ≤ e^{−r}/(16r)`: `Σ_{band} 2Λ(n)/√n ∫ F(x) F(x + log n) dx ≤ T(r − 2δ, r)`; the Lipschitz bound
comes from the compact support. -/
theorem sum_primeShift_le_lightCone_of_contDiff {F : ℝ → ℝ} {r δ : ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0)
    (hr : 2 ≤ r) (hδ0 : 0 < δ) (hδ : δ ≤ Real.exp (-r) / (16 * r)) :
    ∑ n ∈ lightConeBand r δ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
      stripBoxEnergy F (r - 2 * δ) r := by
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport hF hFc
  exact sum_primeShift_le_lightCone hF.continuous hFc hodd (fun a b => hK b a) hsupp hr hδ0 hδ

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
