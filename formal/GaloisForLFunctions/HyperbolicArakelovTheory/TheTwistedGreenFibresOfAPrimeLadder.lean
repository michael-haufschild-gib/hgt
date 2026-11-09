import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePlacesAreTrees
import GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOrbitWeightSummability

/-!
# Twisted Green fibres of a prime ladder

Periodizing the apartment Green kernel by translations of length two loses the
ladder coordinate at the trivial character. The full family of unitary characters
retains it: Fourier coefficients recover every entry of the original tree Green
kernel. Each two-level fibre has an explicit positive Gram decomposition.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped ComplexConjugate
namespace GaloisForLFunctions.HyperbolicArakelovTheory
namespace LadderFloquet

/-- The geometric apartment kernel periodized by the even translation subgroup. -/
def periodized (r : ℝ) (z : ℂ) (n : ℤ) : ℂ :=
  ∑' j : ℤ, ((r ^ (n + 2 * j).natAbs : ℝ) : ℂ) * z ^ j

private theorem coefficient_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℤ) :
    Summable (fun j : ℤ => ‖((r ^ (n + 2 * j).natAbs : ℝ) : ℂ)‖) := by
  have hi : Function.Injective (fun j : ℤ => n + 2 * j) := by
    intro a b hab
    omega
  have h := (_root_.RHTower.summable_pow_natAbs hr0 hr1).comp_injective hi
  exact h.congr fun j => by
    simp only [Function.comp_apply, Complex.norm_real, abs_of_nonneg (pow_nonneg hr0 _)]

/-- Unitary periodization is absolutely convergent. -/
theorem summable_periodized {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (n : ℤ) :
    Summable (fun j : ℤ => ((r ^ (n + 2 * j).natAbs : ℝ) : ℂ) * z ^ j) := by
  apply Summable.of_norm_bounded (coefficient_summable hr0 hr1 n)
  intro j
  rw [norm_mul, norm_zpow, hz, one_zpow, mul_one]

/-- The unitary fibre has the required automorphy under the arithmetic unit. -/
theorem periodized_add_two (r : ℝ) {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    periodized r z (n + 2) = z⁻¹ * periodized r z n := by
  let f : ℤ → ℂ := fun j => ((r ^ (n + 2 * j).natAbs : ℝ) : ℂ) * z ^ j
  have heq : ∀ j : ℤ,
      ((r ^ (n + 2 + 2 * j).natAbs : ℝ) : ℂ) * z ^ j = z⁻¹ * f (j + 1) := by
    intro j
    dsimp only [f]
    rw [show n + 2 * (j + 1) = n + 2 + 2 * j by ring,
      zpow_add₀ hz, zpow_one]
    field_simp
  calc
    periodized r z (n + 2) = ∑' j : ℤ, z⁻¹ * f (j + 1) := tsum_congr heq
    _ = z⁻¹ * ∑' j : ℤ, f (j + 1) := tsum_mul_left
    _ = z⁻¹ * periodized r z n := by
      rw [(Equiv.addRight (1 : ℤ)).tsum_eq f]

private theorem norm_scaled_phase_lt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(r : ℂ) ^ 2 * z‖ < 1 ∧ ‖(r : ℂ) ^ 2 / z‖ < 1 := by
  have hr2 : r ^ 2 < 1 := by
    have h := mul_pos (by linarith only [hr0] : 0 < r + 1) (sub_pos.mpr hr1)
    nlinarith only [h]
  simpa only [norm_mul, norm_div, norm_pow, Complex.norm_real,
    abs_of_nonneg hr0, hz, mul_one, div_one] using And.intro hr2 hr2

private theorem phase_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simpa [h] using hz

private theorem one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using hz

private theorem periodized_parity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (e : ℕ) (he : e ≤ 1) :
    periodized r z e =
      (r : ℂ) ^ e * (1 - (r : ℂ) ^ 2 * z)⁻¹ +
      ((r : ℂ) ^ (2 - e) / z) * (1 - (r : ℂ) ^ 2 / z)⁻¹ := by
  have hz0 := phase_ne_zero hz
  have hnorm := norm_scaled_phase_lt hr0 hr1 hz
  have hp := hasSum_geometric_of_norm_lt_one hnorm.1
  have hn := hasSum_geometric_of_norm_lt_one hnorm.2
  have ep : ∀ j : ℕ,
      ((r ^ ((e : ℤ) + 2 * j).natAbs : ℝ) : ℂ) * z ^ (j : ℤ) =
        (r : ℂ) ^ e * ((r : ℂ) ^ 2 * z) ^ j := by
    intro j
    have habs : ((e : ℤ) + 2 * j).natAbs = e + 2 * j := by omega
    rw [habs, Complex.ofReal_pow, zpow_natCast, pow_add, pow_mul, mul_pow]
    ring
  have en : ∀ j : ℕ,
      ((r ^ ((e : ℤ) + 2 * (-(j + 1 : ℤ))).natAbs : ℝ) : ℂ) * z ^ (-(j + 1 : ℤ)) =
        ((r : ℂ) ^ (2 - e) / z) * ((r : ℂ) ^ 2 / z) ^ j := by
    intro j
    have habs : ((e : ℤ) + 2 * (-(j + 1 : ℤ))).natAbs = 2 * j + (2 - e) := by omega
    have hj : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [habs, Complex.ofReal_pow, hj, zpow_neg, zpow_natCast, pow_add, pow_mul,
      pow_succ z j]
    simp only [mul_inv_rev, inv_pow, div_eq_mul_inv, mul_pow]
    ring
  have hp' : HasSum
      (fun j : ℕ => ((r ^ ((e : ℤ) + 2 * j).natAbs : ℝ) : ℂ) * z ^ (j : ℤ))
      ((r : ℂ) ^ e * (1 - (r : ℂ) ^ 2 * z)⁻¹) := by
    convert hp.mul_left ((r : ℂ) ^ e) using 1
    exact funext ep
  have hn' : HasSum
      (fun j : ℕ => ((r ^ ((e : ℤ) + 2 * (-(j + 1 : ℤ))).natAbs : ℝ) : ℂ) *
        z ^ (-(j + 1 : ℤ)))
      (((r : ℂ) ^ (2 - e) / z) * (1 - (r : ℂ) ^ 2 / z)⁻¹) := by
    convert hn.mul_left ((r : ℂ) ^ (2 - e) / z) using 1
    exact funext en
  rw [periodized, tsum_of_nat_of_neg_add_one hp'.summable hn'.summable,
    hp'.tsum_eq, hn'.tsum_eq]

/-- The denominator of the two-level Green fibre. -/
def denominator (r : ℝ) (z : ℂ) : ℂ :=
  (1 - (r : ℂ) ^ 2 * z) * (1 - (r : ℂ) ^ 2 / z)

/-- The even diagonal entry is a Poisson kernel with ratio `r²`. -/
theorem periodized_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    periodized r z 0 = (1 - (r : ℂ) ^ 4) / denominator r z := by
  have hnorm := norm_scaled_phase_lt hr0 hr1 hz
  have ha := one_sub_ne_zero_of_norm_lt_one hnorm.1
  have hb := one_sub_ne_zero_of_norm_lt_one hnorm.2
  have hz0 := phase_ne_zero hz
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, periodized_parity hr0 hr1 hz 0 (by omega)]
  simp only [pow_zero, Nat.sub_zero, one_mul, denominator]
  field_simp [ha, hb, hz0]
  ring

/-- The odd entry contains the transition between the two parity classes. -/
theorem periodized_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    periodized r z 1 =
      (r : ℂ) * (1 - (r : ℂ) ^ 2) * (1 + z⁻¹) / denominator r z := by
  have hnorm := norm_scaled_phase_lt hr0 hr1 hz
  have ha := one_sub_ne_zero_of_norm_lt_one hnorm.1
  have hb := one_sub_ne_zero_of_norm_lt_one hnorm.2
  have hz0 := phase_ne_zero hz
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, periodized_parity hr0 hr1 hz 1 le_rfl]
  norm_num only [pow_one, Nat.reduceSub]
  unfold denominator
  field_simp [ha, hb, hz0]
  ring

private theorem inv_eq_conj_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z⁻¹ = conj z := by
  have hp : z * conj z = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  exact mul_left_cancel₀ (phase_ne_zero hz) ((mul_inv_cancel₀ (phase_ne_zero hz)).trans hp.symm)

/-- On the unitary circle the denominator is a strictly positive squared norm. -/
theorem denominator_eq_normSq {z : ℂ} (hz : ‖z‖ = 1) (r : ℝ) :
    denominator r z = (Complex.normSq (1 - (r : ℂ) ^ 2 * z) : ℂ) := by
  rw [denominator, div_eq_mul_inv, inv_eq_conj_of_norm_one hz, ← Complex.mul_conj]
  congr 1
  simp only [map_sub, map_one, map_mul, map_pow, Complex.conj_ofReal]

private theorem gram_identity (r : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (u v : ℂ) :
    Complex.normSq (u + r * v) + Complex.normSq (r * u + z * v) =
      (1 + r ^ 2) * (Complex.normSq u + Complex.normSq v) +
        2 * r * (((1 + conj z) * u * conj v).re) := by
  have hzz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz, one_pow, Complex.normSq_apply] at h
    simpa only [pow_two] using h
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  linear_combination (v.re ^ 2 + v.im ^ 2) * hzz

/-- Exact positive Gram decomposition of the two-level twisted Green matrix. -/
theorem fibre_gram {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ = 1)
    (u v : ℂ) :
    (periodized r z 0).re * (Complex.normSq u + Complex.normSq v) +
      2 * (periodized r z 1 * u * conj v).re =
    ((1 - r ^ 2) / Complex.normSq (1 - (r : ℂ) ^ 2 * z)) *
      (Complex.normSq (u + r * v) + Complex.normSq (r * u + z * v)) := by
  let D : ℝ := Complex.normSq (1 - (r : ℂ) ^ 2 * z)
  have he : periodized r z 0 = (((1 - r ^ 2) * (1 + r ^ 2) / D : ℝ) : ℂ) := by
    rw [periodized_zero hr0 hr1 hz, denominator_eq_normSq hz]
    push_cast
    ring
  have ho : periodized r z 1 = ((r * (1 - r ^ 2) / D : ℝ) : ℂ) * (1 + conj z) := by
    rw [periodized_one hr0 hr1 hz, denominator_eq_normSq hz, inv_eq_conj_of_norm_one hz]
    push_cast
    ring
  rw [he, ho, Complex.ofReal_re, gram_identity r hz]
  have hcross : (((r * (1 - r ^ 2) / D : ℝ) : ℂ) * (1 + conj z) * u * conj v).re =
      (r * (1 - r ^ 2) / D) * (((1 + conj z) * u * conj v).re) := by
    rw [mul_assoc, mul_assoc, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hcross]
  dsimp only [D]
  ring

/-- Every unitary two-level fibre is positive definite. -/
theorem fibre_energy_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ = 1)
    (u v : ℂ) (hne : u ≠ 0 ∨ v ≠ 0) :
    0 < (periodized r z 0).re * (Complex.normSq u + Complex.normSq v) +
      2 * (periodized r z 1 * u * conj v).re := by
  rw [fibre_gram hr0 hr1 hz]
  have hr2 : r ^ 2 < 1 := by
    have h := mul_pos (by linarith only [hr0] : 0 < r + 1) (sub_pos.mpr hr1)
    nlinarith only [h]
  have hden : 0 < Complex.normSq (1 - (r : ℂ) ^ 2 * z) :=
    Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one (norm_scaled_phase_lt hr0 hr1 hz).1)
  apply mul_pos (div_pos (sub_pos.mpr hr2) hden)
  have h1 := Complex.normSq_nonneg (u + r * v)
  have h2 := Complex.normSq_nonneg (r * u + z * v)
  by_contra hnot
  have hsum : Complex.normSq (u + r * v) + Complex.normSq (r * u + z * v) ≤ 0 :=
    not_lt.mp hnot
  have he1 : u + (r : ℂ) * v = 0 := Complex.normSq_eq_zero.mp (by linarith only [h1, h2, hsum])
  have he2 : (r : ℂ) * u + z * v = 0 := Complex.normSq_eq_zero.mp (by linarith only [h1, h2, hsum])
  have hz2 : z - (r : ℂ) ^ 2 ≠ 0 := by
    intro h
    have heq : z = (r : ℂ) ^ 2 := sub_eq_zero.mp h
    have hn := congrArg norm heq
    rw [hz, norm_pow, Complex.norm_real, abs_of_nonneg hr0] at hn
    linarith only [hn, hr2]
  have hv : (z - (r : ℂ) ^ 2) * v = 0 := by linear_combination he2 - (r : ℂ) * he1
  have hv0 : v = 0 := (mul_eq_zero.mp hv).resolve_left hz2
  have hu0 : u = 0 := by simpa only [hv0, mul_zero, add_zero] using he1
  exact hne.elim (fun h => h hu0) (fun h => h hv0)

/-- A coordinate on the unitary character circle. -/
def phase (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * θ)

theorem norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

private theorem phase_zpow (θ : ℝ) (j : ℤ) :
    phase θ ^ j = _root_.RHTower.deningerCharacter 1 j θ := by
  rw [phase, ← Complex.exp_int_mul, _root_.RHTower.deningerCharacter_apply]
  congr 1
  push_cast
  ring

/-- Every original ladder coefficient is recovered from the character family. -/
theorem fourierCoeff_periodized {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n j : ℤ) :
    _root_.RHTower.deningerFourierCoeff 1 (fun θ => periodized r (phase θ) n) j =
      ((r ^ (n + 2 * j).natAbs : ℝ) : ℂ) := by
  simp only [periodized, phase_zpow]
  exact GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman.coeff_tsum_characters
    one_pos (coefficient_summable hr0 hr1 n) j

/-- The actual tree Green function, periodized over the arithmetic unit. -/
def treeFibre (q s : ℝ) (n : ℤ) (θ : ℝ) : ℂ :=
  ∑' j : ℤ, (treeGreen q s (n + 2 * j).natAbs : ℂ) * phase θ ^ j

/-- The whole tree Green kernel survives in two parity fibres and their Fourier coefficients. -/
theorem fourierCoeff_treeFibre {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (n j : ℤ) :
    _root_.RHTower.deningerFourierCoeff 1 (treeFibre q s n) j =
      (treeGreen q s (n + 2 * j).natAbs : ℂ) := by
  have hr0 : 0 ≤ q ^ (-s) := Real.rpow_nonneg (by linarith only [hq]) _
  have hr1 : q ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  have hsum : Summable (fun j : ℤ => ‖(treeGreen q s (n + 2 * j).natAbs : ℂ)‖) := by
    have h := (coefficient_summable hr0 hr1 n).mul_left
      ‖((q ^ s / (q ^ (2 * s) - 1) : ℝ) : ℂ)‖
    simpa only [treeGreen, Complex.ofReal_mul, norm_mul] using h
  simp only [treeFibre, phase_zpow]
  exact GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman.coeff_tsum_characters
    one_pos hsum j

/-- Only the two parity fibres are needed to reconstruct the entire apartment. -/
theorem treeGreen_eq_two_fibre_coefficient {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (k : ℕ) :
    (treeGreen q s k : ℂ) =
      _root_.RHTower.deningerFourierCoeff 1 (treeFibre q s (k % 2)) (k / 2) := by
  rw [fourierCoeff_treeFibre hq hs]
  have he : ((k % 2 : ℕ) : ℤ) + 2 * ((k / 2 : ℕ) : ℤ) = (k : ℤ) := by
    exact_mod_cast Nat.mod_add_div k 2
  rw [he, Int.natAbs_natCast]

theorem treeFibre_eq (q s : ℝ) (n : ℤ) (θ : ℝ) :
    treeFibre q s n θ = ((q ^ s / (q ^ (2 * s) - 1) : ℝ) : ℂ) *
      periodized (q ^ (-s)) (phase θ) n := by
  simp only [treeFibre, treeGreen, Complex.ofReal_mul, periodized, mul_assoc, tsum_mul_left]

/-- Every unitary fibre of the actual tree Green kernel is positive definite, including at
its critical spectral parameter. -/
theorem treeFibre_energy_pos {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (θ : ℝ)
    (u v : ℂ) (hne : u ≠ 0 ∨ v ≠ 0) :
    0 < (treeFibre q s 0 θ).re * (Complex.normSq u + Complex.normSq v) +
      2 * (treeFibre q s 1 θ * u * conj v).re := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hr0 : 0 ≤ q ^ (-s) := Real.rpow_nonneg hq0.le _
  have hr1 : q ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  have hc : 0 < q ^ s / (q ^ (2 * s) - 1) :=
    div_pos (Real.rpow_pos_of_pos hq0 s)
      (sub_pos.mpr (Real.one_lt_rpow hq (by linarith only [hs])))
  have h := mul_pos hc (fibre_energy_pos hr0 hr1 (norm_phase θ) u v hne)
  rw [treeFibre_eq, treeFibre_eq]
  simpa only [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_add, mul_left_comm] using h

/-- Specialization to the critical parameter recovers Weil's prime-ladder entry. -/
theorem weilPrimeKernel_eq_treeFibre_coefficient {p m k : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hk : 1 ≤ k) :
    (ArithmeticEffectivityTheory.weilPrimeKernel m (m * p ^ k) : ℂ) =
      (Real.log p * (((p : ℝ) - 1) / Real.sqrt p) : ℝ) *
        _root_.RHTower.deningerFourierCoeff 1 (treeFibre p (1 / 2) (k % 2)) (k / 2) := by
  rw [← treeGreen_eq_two_fibre_coefficient (by exact_mod_cast hp.one_lt) (by norm_num)]
  rw [weilPrimeKernel_mul_pow_eq_treeGreen hp hm hk, Complex.ofReal_mul]

#print axioms periodized_add_two
#print axioms fourierCoeff_periodized
#print axioms fibre_gram
#print axioms fibre_energy_pos
#print axioms treeFibre_energy_pos
#print axioms treeGreen_eq_two_fibre_coefficient
#print axioms fourierCoeff_treeFibre
#print axioms weilPrimeKernel_eq_treeFibre_coefficient

end LadderFloquet
end GaloisForLFunctions.HyperbolicArakelovTheory
