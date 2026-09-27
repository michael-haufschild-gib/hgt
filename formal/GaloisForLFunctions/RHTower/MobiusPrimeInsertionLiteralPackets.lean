import GaloisForLFunctions.RHTower.MobiusPrimeInsertionDipoleJet
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Literal Möbius realizations of the prime-insertion jets

The prime number theorem places primes `p_r ∈ (2r, (1+ε)2r)` for every large prime `r`, so the
four squarefree integers `p_r, 2r, 3p_r, 6r` carry Möbius signs `-1, +1, +1, -1` and form the
literal packet `-(D_3 f_(p_r) - D_3 f_(2r))`.  Its insertion-energy ratio relative to the
prime/semiprime precursor tends to `R_3 = 283/192`.  Choosing four primes on a diagonal scale
`ε_j = 1/j` realizes the positive dyadic mechanism: the literal two-dipole precursor and its
`2`-inserted eight-atom packet have energy ratio tending to the quotient of card equation (5),
strictly below `4/5`.
-/

open Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-! ### Möbius signs of the literal atoms -/

theorem moebius_mul_prime {q p : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) : μ (q * p) = -μ q := by
  have hcop : Nat.Coprime q p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hq).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

private theorem not_dvd_of_lt_prime {p q : ℕ} (_hp : p.Prime) (hq0 : 0 < q) (hlt : q < p) :
    ¬ p ∣ q := fun h => absurd (Nat.le_of_dvd hq0 h) (by omega)

theorem moebius_prime (p : ℕ) (hp : p.Prime) : μ p = -1 :=
  ArithmeticFunction.moebius_apply_prime hp

theorem moebius_two_mul {r : ℕ} (hr : r.Prime) (h2 : 2 < r) : μ (2 * r) = 1 := by
  rw [moebius_mul_prime hr (not_dvd_of_lt_prime hr (by norm_num) h2), moebius_prime 2 Nat.prime_two]
  norm_num

theorem moebius_three_mul {r : ℕ} (hr : r.Prime) (h3 : 3 < r) : μ (3 * r) = 1 := by
  rw [moebius_mul_prime hr (not_dvd_of_lt_prime hr (by norm_num) h3), moebius_prime 3 Nat.prime_three]
  norm_num

theorem moebius_six_mul {r : ℕ} (hr : r.Prime) (h6 : 6 < r) : μ (6 * r) = -1 := by
  rw [moebius_mul_prime hr (not_dvd_of_lt_prime hr (by norm_num) h6),
    show (6 : ℕ) = 3 * 2 by norm_num,
    moebius_mul_prime Nat.prime_two (by norm_num), moebius_prime 3 Nat.prime_three]
  norm_num

theorem moebius_two_mul_prime' {p : ℕ} (hp : p.Prime) (h2 : 2 < p) : μ (2 * p) = 1 :=
  moebius_two_mul hp h2

/-! ### Energy convergence from norm convergence -/

/-- If `‖F_j/ε_j + G‖ → 0` then `‖F_j‖²/ε_j² → ‖G‖²`. -/
theorem tendsto_gammaEnergy_div_sq_seq {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hF : ∀ j, GammaFinite δ (F j)) (hG : GammaFinite δ G)
    (hlim : Tendsto (fun j => gammaNorm δ (fun t => F j t / ε j + G t)) atTop (𝓝 0)) :
    Tendsto (fun j => gammaEnergy δ (F j) / ε j ^ 2) atTop (𝓝 (gammaEnergy δ G)) := by
  have hFh : ∀ j, GammaFinite δ (fun t => F j t / ε j) := fun j => by
    simpa [div_eq_mul_inv, mul_comm] using (hF j).smul (ε j)⁻¹
  have hnorm : Tendsto (fun j => gammaNorm δ (fun t => F j t / ε j)) atTop
      (𝓝 (gammaNorm δ G)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
    rw [Real.norm_eq_abs]
    have h := abs_gammaNorm_sub_le hδ (hFh j) hG.neg
    rw [gammaNorm_neg hδ hG] at h
    simpa [sub_neg_eq_add] using h
  have hsq := hnorm.pow 2
  rw [gammaNorm_sq hδ hG] at hsq
  refine hsq.congr fun j => ?_
  rw [gammaNorm_sq hδ (hFh j)]
  have hj : ε j ≠ 0 := (hε j).ne'
  have e : (fun t => F j t / ε j) = fun t => (ε j)⁻¹ * F j t := by funext t; ring
  rw [e, gammaEnergy, gammaInner_smul_left hδ (hF j) ((hF j).smul _),
    gammaInner_smul_right hδ (hF j) (hF j), ← gammaEnergy]
  field_simp

/-! ### The literal four-atom packet -/

/-- The literal four-atom packet `-f_p + f_(2r) + f_(3p) - f_(6r)`. -/
def fourAtomPacket (r p : ℕ) (t : ℝ) : ℝ :=
  -atom p t + atom (2 * r) t + atom (3 * p) t - atom (6 * r) t

/-- The prime/semiprime precursor `f_(2r) - f_p`. -/
def primeSemiprimeDipole (r p : ℕ) (t : ℝ) : ℝ := atom (2 * r) t - atom p t

theorem fourAtomPacket_eq_insertion (r p : ℕ) :
    fourAtomPacket r p = fun t =>
      -((atom p t - atom (3 * p) t) - (atom (2 * r) t - atom (3 * (2 * r)) t)) := by
  funext t
  unfold fourAtomPacket
  rw [show (3 : ℝ) * (2 * r) = 6 * r by ring]
  ring

/-- The literal four-atom ratio is the insertion ratio of `f_p - f_(2r)`. -/
theorem fourAtom_ratio_eq {r p : ℕ} (hr : 0 < r) (hp : 2 * r < p) :
    gammaEnergy 0 (fourAtomPacket r p) / gammaEnergy 0 (primeSemiprimeDipole r p) =
      insertionEnergyRatio 0 3 1 (((p : ℝ) - 2 * r) / (2 * r)) := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hx : (0 : ℝ) < 2 * r := by positivity
  rw [← insertionEnergyRatio_scale 0 3 hx]
  have hpx : (2 * (r : ℝ) + ((p : ℝ) - 2 * r)) = p := by ring
  have hA : primeSemiprimeDipole r p = fun t => -(nearDipole (2 * r) ((p : ℝ) - 2 * r) t) := by
    funext t; unfold primeSemiprimeDipole nearDipole; rw [hpx]; ring
  have hB : fourAtomPacket r p = fun t =>
      -(insertedDipole 3 (2 * r) ((p : ℝ) - 2 * r) t) := by
    rw [fourAtomPacket_eq_insertion]
    funext t; unfold insertedDipole; rw [hpx]
  have hp0 : (0 : ℝ) < p := by
    have : (2 * r : ℝ) < p := by exact_mod_cast hp
    linarith
  have fA : GammaFinite 0 (nearDipole (2 * r) ((p : ℝ) - 2 * r)) := by
    unfold nearDipole; rw [hpx]
    exact (gammaFinite_atom hδ hp0).sub (gammaFinite_atom hδ hx)
  have fB : GammaFinite 0 (insertedDipole 3 (2 * r) ((p : ℝ) - 2 * r)) := by
    unfold insertedDipole; rw [hpx]
    exact ((gammaFinite_atom hδ hp0).sub (gammaFinite_atom hδ (by positivity))).sub
      ((gammaFinite_atom hδ hx).sub (gammaFinite_atom hδ (by positivity)))
  unfold insertionEnergyRatio
  rw [hA, hB, gammaEnergy, gammaEnergy, show (fun t => -nearDipole (2 * ↑r) (↑p - 2 * ↑r) t) =
    fun t => (-1) * nearDipole (2 * ↑r) (↑p - 2 * ↑r) t by funext t; ring,
    show (fun t => -insertedDipole 3 (2 * ↑r) (↑p - 2 * ↑r) t) =
      fun t => (-1) * insertedDipole 3 (2 * ↑r) (↑p - 2 * ↑r) t by funext t; ring,
    gammaInner_smul_left hδ fA (fA.smul _), gammaInner_smul_right hδ fA fA,
    gammaInner_smul_left hδ fB (fB.smul _), gammaInner_smul_right hδ fB fB]
  unfold gammaEnergy
  by_cases h0 : gammaInner 0 (nearDipole (2 * ↑r) (↑p - 2 * ↑r))
    (nearDipole (2 * ↑r) (↑p - 2 * ↑r)) = 0
  · rw [h0]; simp
  · field_simp

/-- **Literal Möbius occurrence.**  There are primes `r_j → ∞` and `p_j ∈ (2 r_j, ∞)` with
`p_j/(2 r_j) → 1`; the atoms `p_j, 2r_j, 3p_j, 6r_j` carry Möbius signs `-1, +1, +1, -1`, the
literal packet is `-(D_3 f_(p_j) - D_3 f_(2r_j))`, and its insertion-energy ratio relative to the
precursor tends to `283/192`. -/
theorem exists_literal_fourAtom_sequence :
    ∃ r p : ℕ → ℕ, (∀ j, (r j).Prime ∧ (p j).Prime ∧ 6 < r j ∧ 2 * r j < p j ∧ j ≤ r j) ∧
      Tendsto (fun j => (p j : ℝ) / (2 * r j)) atTop (𝓝 1) ∧
      (∀ j, μ (p j) = -1 ∧ μ (2 * r j) = 1 ∧ μ (3 * p j) = 1 ∧ μ (6 * r j) = -1) ∧
      Tendsto (fun j => gammaEnergy 0 (fourAtomPacket (r j) (p j)) /
        gammaEnergy 0 (primeSemiprimeDipole (r j) (p j))) atTop (𝓝 (283 / 192)) := by
  have hchoice : ∀ j : ℕ, ∃ rp : ℕ × ℕ, rp.1.Prime ∧ rp.2.Prime ∧ 6 < rp.1 ∧ 2 * rp.1 < rp.2 ∧
      j ≤ rp.1 ∧ (rp.2 : ℝ) < (1 + 1 / ((j : ℝ) + 1)) * (2 * rp.1) := by
    intro j
    have hev := prime_between (ε := 1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨X, hX⟩ := eventually_atTop.mp hev
    obtain ⟨r, hr1, hr⟩ := Nat.exists_infinite_primes (max (max j 7) (⌈X⌉₊))
    have hrX : X ≤ 2 * (r : ℝ) := by
      have : (⌈X⌉₊ : ℝ) ≤ r := by exact_mod_cast (le_max_right _ _).trans hr1
      have := Nat.le_ceil X
      have : (0 : ℝ) ≤ r := by positivity
      linarith
    obtain ⟨p, hp, hlo, hhi⟩ := hX (2 * r) hrX
    refine ⟨(r, p), hr, hp, ?_, ?_, ?_, hhi⟩
    · have := (le_max_right _ _).trans ((le_max_left _ _).trans hr1); omega
    · exact_mod_cast hlo
    · exact (le_max_left _ _).trans ((le_max_left _ _).trans hr1)
  choose rp hrp using hchoice
  refine ⟨fun j => (rp j).1, fun j => (rp j).2, fun j => ⟨(hrp j).1, (hrp j).2.1, (hrp j).2.2.1,
    (hrp j).2.2.2.1, (hrp j).2.2.2.2.1⟩, ?_, fun j => ?_, ?_⟩
  · -- the ratio `p/(2r) → 1`
    have hlow : ∀ j, (1 : ℝ) ≤ ((rp j).2 : ℝ) / (2 * (rp j).1) := by
      intro j
      have h1 := (hrp j).2.2.2.1
      have h6 := (hrp j).2.2.1
      have h2 : (2 * (rp j).1 : ℝ) < (rp j).2 := by exact_mod_cast h1
      have : (0 : ℝ) < 2 * (rp j).1 := by
        have : (0 : ℝ) < (rp j).1 := by exact_mod_cast (by omega : 0 < (rp j).1)
        linarith
      rw [le_div_iff₀ this]; linarith
    have hup : ∀ j, ((rp j).2 : ℝ) / (2 * (rp j).1) ≤ 1 + 1 / ((j : ℝ) + 1) := by
      intro j
      have h := (hrp j).2.2.2.2.2
      have h6 := (hrp j).2.2.1
      have : (0 : ℝ) < 2 * (rp j).1 := by
        have : (0 : ℝ) < (rp j).1 := by exact_mod_cast (by omega : 0 < (rp j).1)
        linarith
      rw [div_le_iff₀ this]; linarith
    have hlim : Tendsto (fun j : ℕ => (1 : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 1) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlow hup
  · obtain ⟨hr, hp, h6, hpr, -⟩ := hrp j
    show μ (rp j).2 = -1 ∧ μ (2 * (rp j).1) = 1 ∧ μ (3 * (rp j).2) = 1 ∧ μ (6 * (rp j).1) = -1
    exact ⟨moebius_prime _ hp, moebius_two_mul hr (by omega), moebius_three_mul hp (by omega),
      moebius_six_mul hr h6⟩
  · -- the energy ratio tends to `R_3`
    have hx : ∀ j, (0 : ℝ) < ((rp j).2 : ℝ) / (2 * (rp j).1) - 1 := by
      intro j
      have h2 : (2 * (rp j).1 : ℝ) < (rp j).2 := by exact_mod_cast (hrp j).2.2.2.1
      have h6 := (hrp j).2.2.1
      have : (0 : ℝ) < 2 * (rp j).1 := by
        have : (0 : ℝ) < (rp j).1 := by exact_mod_cast (by omega : 0 < (rp j).1)
        linarith
      rw [sub_pos, lt_div_iff₀ this]; linarith
    have hup : ∀ j, ((rp j).2 : ℝ) / (2 * (rp j).1) - 1 ≤ 1 / ((j : ℝ) + 1) := by
      intro j
      have h := (hrp j).2.2.2.2.2
      have h6 := (hrp j).2.2.1
      have : (0 : ℝ) < 2 * (rp j).1 := by
        have : (0 : ℝ) < (rp j).1 := by exact_mod_cast (by omega : 0 < (rp j).1)
        linarith
      rw [sub_le_iff_le_add, div_le_iff₀ this]; linarith
    have hto : Tendsto (fun j => ((rp j).2 : ℝ) / (2 * (rp j).1) - 1) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hx⟩
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun j => (hx j).le) hup
    have hmain := (tendsto_insertionEnergyRatio (q := 3) (x := 1) (by norm_num) one_pos).comp hto
    rw [insertionRatio_three] at hmain
    refine hmain.congr fun j => ?_
    have hr0 : 0 < (rp j).1 := by have := (hrp j).2.2.1; omega
    rw [Function.comp_apply, fourAtom_ratio_eq hr0 (hrp j).2.2.2.1]
    congr 1
    have : (0 : ℝ) < 2 * (rp j).1 := by positivity
    field_simp

/-! ### First-jet approximation of dipoles -/

/-- `‖∂f_x‖_δ ≤ C_1 x^(-(3+δ)/2)`. -/
theorem gammaNorm_atomJet_one_le' {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx : 0 < x) :
    gammaNorm δ (atomJet 1 x) ≤ jetConst 1 * x ^ (-(3 + δ) / 2) := by
  refine (gammaNorm_atomJet_le hδ0 hδ1 1 hx).trans (le_of_eq ?_)
  rw [pow_one, show -(3 + δ) / 2 = 1 + -((5 + δ) / 2) by ring, Real.rpow_add hx, Real.rpow_one,
    Real.rpow_neg hx.le]
  field_simp

/-- `‖v_x‖_δ ≤ C_1 x^(-(1+δ)/2)`. -/
theorem gammaNorm_jetProfile_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx : 0 < x) :
    gammaNorm δ (jetProfile x) ≤ jetConst 1 * x ^ (-(1 + δ) / 2) := by
  have hδ : 0 < 5 + δ := by linarith
  unfold jetProfile
  rw [gammaNorm_smul hδ (gammaFinite_atomJet hδ 1 hx), abs_of_pos hx]
  refine (mul_le_mul_of_nonneg_left (gammaNorm_atomJet_one_le' hδ0 hδ1 hx) hx.le).trans
    (le_of_eq ?_)
  rw [show -(1 + δ) / 2 = 1 + -(3 + δ) / 2 by ring, Real.rpow_add hx, Real.rpow_one]
  ring

/-- **Dipole approximation.**  `‖(f_x - f_(x(1+e))) + e v_x‖_δ ≤ 2 C_2 x^(-(1+δ)/2) e²`
for `0 ≤ e ≤ 1`. -/
theorem gammaNorm_dipole_add_jetProfile_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x e : ℝ}
    (hx : 0 < x) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    gammaNorm δ (fun t => (atom x t - atom (x * (1 + e)) t) + e * jetProfile x t) ≤
      2 * jetConst 2 * x ^ (-(1 + δ) / 2) * e ^ 2 := by
  have hδ : 0 < 5 + δ := by linarith
  have hxe : x ≤ x * (1 + e) := by nlinarith
  have e1 : (fun t => (atom x t - atom (x * (1 + e)) t) + e * jetProfile x t) =
      fun t => -taylorRem 2 x (x * (1 + e)) t := by
    funext t
    unfold taylorRem jetProfile
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, atomJet_zero, Nat.factorial]
    ring
  rw [e1, gammaNorm_neg hδ (gammaFinite_taylorRem hδ 2 hx hxe)]
  refine (gammaNorm_taylorRem_le hδ0 hδ1 2 hx hxe).trans ?_
  have hC := jetConst_nonneg 2
  have hxp : x ^ (-(1 + δ) / 2) = x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hx.le, ← Real.rpow_natCast, ← Real.rpow_add hx]; ring_nf
  rw [hxp]
  have h1e : (1 + e) ^ 2 ≤ 4 := by nlinarith
  have hp : 0 < (x ^ ((5 + δ) / 2))⁻¹ := by positivity
  calc (x * (1 + e) - x) ^ 2 / ((2 : ℕ).factorial : ℝ) *
        (jetConst 2 * (x * (1 + e)) ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ 2)
      = e ^ 2 / 2 * (jetConst 2 * (1 + e) ^ 2 * (x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹)) := by
        simp only [Nat.factorial]; field_simp; ring
    _ ≤ e ^ 2 / 2 * (jetConst 2 * 4 * (x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹)) := by gcongr
    _ = 2 * jetConst 2 * (x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹) * e ^ 2 := by ring

/-- **Profile Lipschitz law.**  For `0 < a ≤ b`,
`‖v_b - v_a‖_δ ≤ (b-a) (C_1 b a^(-(5+δ)/2) + C_2 b² a^(-(5+δ)/2) / a)`. -/
theorem gammaNorm_jetProfile_sub_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    gammaNorm δ (fun t => jetProfile b t - jetProfile a t) ≤
      (b - a) * (jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a +
        jetConst 2 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a ^ 2 * a) := by
  have hδ : 0 < 5 + δ := by linarith
  have hb : 0 < b := ha.trans_le hab
  have e1 : (fun t => jetProfile b t - jetProfile a t) =
      fun t => (b - a) * atomJet 1 b t + a * jetTaylorRem 1 1 a b t := by
    funext t
    unfold jetProfile jetTaylorRem
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    ring
  rw [e1]
  refine (gammaNorm_add_le hδ ((gammaFinite_atomJet hδ 1 hb).smul _)
    ((gammaFinite_jetTaylorRem hδ 1 1 ha hab).smul _)).trans ?_
  rw [gammaNorm_smul hδ (gammaFinite_atomJet hδ 1 hb),
    gammaNorm_smul hδ (gammaFinite_jetTaylorRem hδ 1 1 ha hab), abs_of_nonneg (by linarith),
    abs_of_pos ha]
  have h1 := gammaNorm_atomJet_le hδ0 hδ1 1 hb
  have h2 := gammaNorm_jetTaylorRem_le hδ0 hδ1 1 1 ha hab
  have hmono : (b ^ ((5 + δ) / 2))⁻¹ ≤ (a ^ ((5 + δ) / 2))⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hab (by linarith))
  have hC1 := jetConst_nonneg 1
  have hC2 := jetConst_nonneg 2
  have t1 : gammaNorm δ (atomJet 1 b) ≤ jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a := by
    refine h1.trans ?_
    rw [pow_one]
    calc jetConst 1 * b ^ 2 * (b ^ ((5 + δ) / 2))⁻¹ / b
        ≤ jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / b := by gcongr
      _ ≤ jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a := by gcongr
  have t2 : gammaNorm δ (jetTaylorRem 1 1 a b) ≤
      (b - a) * (jetConst 2 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a ^ 2) := by
    refine h2.trans (le_of_eq ?_)
    norm_num
  calc (b - a) * gammaNorm δ (atomJet 1 b) + a * gammaNorm δ (jetTaylorRem 1 1 a b)
      ≤ (b - a) * (jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a) +
          a * ((b - a) * (jetConst 2 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- **Scaled dipole approximation.**  For `0 < x ≤ y`, `0 ≤ e ≤ 1`, `ε > 0`,
`‖(f_y - f_(y(1+e)))/ε + v_x‖_δ` is bounded by the three first-jet errors. -/
theorem gammaNorm_dipole_div_add_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y e ε : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hε : 0 < ε) :
    gammaNorm δ (fun t => (atom y t - atom (y * (1 + e)) t) / ε + jetProfile x t) ≤
      2 * jetConst 2 * y ^ (-(1 + δ) / 2) * e ^ 2 / ε +
        |1 - e / ε| * (jetConst 1 * y ^ (-(1 + δ) / 2)) +
        (y - x) * (jetConst 1 * y ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x +
          jetConst 2 * y ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ 2 * x) := by
  have hδ : 0 < 5 + δ := by linarith
  have hy : 0 < y := hx.trans_le hxy
  have hye : 0 < y * (1 + e) := by positivity
  have fD : GammaFinite δ (fun t => (atom y t - atom (y * (1 + e)) t) + e * jetProfile y t) :=
    ((gammaFinite_atom hδ hy).sub (gammaFinite_atom hδ hye)).add
      ((gammaFinite_jetProfile hδ hy).smul e)
  have fV := gammaFinite_jetProfile hδ hy
  have fW : GammaFinite δ (fun t => jetProfile y t - jetProfile x t) :=
    fV.sub (gammaFinite_jetProfile hδ hx)
  have e1 : (fun t => (atom y t - atom (y * (1 + e)) t) / ε + jetProfile x t) =
      fun t => (ε⁻¹ * ((atom y t - atom (y * (1 + e)) t) + e * jetProfile y t) +
        (1 - e / ε) * jetProfile y t) + (-1) * (jetProfile y t - jetProfile x t) := by
    funext t; field_simp; ring
  rw [e1]
  refine (gammaNorm_add_le hδ ((fD.smul _).add (fV.smul _)) (fW.smul _)).trans ?_
  refine add_le_add ((gammaNorm_add_le hδ (fD.smul _) (fV.smul _)).trans (add_le_add ?_ ?_)) ?_
  · rw [gammaNorm_smul hδ fD, abs_inv, abs_of_pos hε]
    have := gammaNorm_dipole_add_jetProfile_le hδ0 hδ1 hy he0 he1
    calc ε⁻¹ * gammaNorm δ (fun t => (atom y t - atom (y * (1 + e)) t) + e * jetProfile y t)
        ≤ ε⁻¹ * (2 * jetConst 2 * y ^ (-(1 + δ) / 2) * e ^ 2) := by gcongr
      _ = _ := by ring
  · rw [gammaNorm_smul hδ fV]
    exact mul_le_mul_of_nonneg_left (gammaNorm_jetProfile_le hδ0 hδ1 hy) (abs_nonneg _)
  · rw [gammaNorm_smul hδ fW, abs_neg, abs_one, one_mul]
    exact gammaNorm_jetProfile_sub_le hδ0 hδ1 hx hxy

/-! ### The literal positive dyadic mechanism -/

/-- The literal two-dipole precursor `f_(a₀) - f_(b₀) + f_(a₁) - f_(b₁)`. -/
def twoDipolePrecursor (a₀ b₀ a₁ b₁ t : ℝ) : ℝ := atom a₀ t - atom b₀ t + atom a₁ t - atom b₁ t

/-- The insertion `D_2 F = F - U_2 F`. -/
def insertTwo (F : ℝ → ℝ) (t : ℝ) : ℝ := F t - dilate 2 F t

theorem insertTwo_twoDipolePrecursor (a₀ b₀ a₁ b₁ t : ℝ) :
    insertTwo (twoDipolePrecursor a₀ b₀ a₁ b₁) t =
      atom a₀ t - atom (2 * a₀) t - atom b₀ t + atom (2 * b₀) t +
        atom a₁ t - atom (2 * a₁) t - atom b₁ t + atom (2 * b₁) t := by
  unfold insertTwo twoDipolePrecursor
  have h : ∀ a, dilate 2 (atom a) t = atom (2 * a) t := fun a => by rw [dilate_atom]
  simp only [dilate] at h ⊢
  rw [mul_sub, mul_add, mul_sub, h, h, h, h]
  ring

theorem twoDipolePrecursor_scale {X : ℝ} (a₀ b₀ a₁ b₁ : ℝ) :
    twoDipolePrecursor (X * a₀) (X * b₀) (X * a₁) (X * b₁) =
      dilate X (twoDipolePrecursor a₀ b₀ a₁ b₁) := by
  funext t
  unfold twoDipolePrecursor dilate
  rw [mul_sub, mul_add, mul_sub, atom_scale, atom_scale, atom_scale, atom_scale]

theorem insertTwo_dilate (X : ℝ) (F : ℝ → ℝ) :
    insertTwo (dilate X F) = dilate X (insertTwo F) := by
  funext t
  unfold insertTwo dilate
  rw [show X * (2 * t) = 2 * (X * t) by ring]
  ring

theorem gammaFinite_twoDipolePrecursor {δ : ℝ} (hδ : 0 < 5 + δ) {a₀ b₀ a₁ b₁ : ℝ}
    (h0 : 0 < a₀) (h1 : 0 < b₀) (h2 : 0 < a₁) (h3 : 0 < b₁) :
    GammaFinite δ (twoDipolePrecursor a₀ b₀ a₁ b₁) :=
  (((gammaFinite_atom hδ h0).sub (gammaFinite_atom hδ h1)).add (gammaFinite_atom hδ h2)).sub
    (gammaFinite_atom hδ h3)

theorem gammaFinite_insertTwo {δ : ℝ} {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    GammaFinite δ (insertTwo F) :=
  hF.sub (hF.dilate two_pos)

/-- `‖D_2 F‖_δ ≤ 2 ‖F‖_δ`. -/
theorem gammaNorm_insertTwo_le {δ : ℝ} (hδ : 0 ≤ δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) :
    gammaNorm δ (insertTwo F) ≤ 2 * gammaNorm δ F := by
  have hδ' : 0 < 5 + δ := by linarith
  refine (gammaNorm_sub_dilate_le hδ' two_pos hF).trans ?_
  have : (2 : ℝ) ^ (-(1 + δ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (by linarith)
  have h0 := gammaNorm_nonneg δ F
  nlinarith

/-- The limiting quotient of card equation (5). -/
def dyadicQuotient : ℝ := (45 / 32 + 23040 / 78125) / (27 / 16 + 128 / 243)

theorem dyadicQuotient_lt : dyadicQuotient < 4 / 5 := by
  unfold dyadicQuotient; norm_num

theorem dyadicQuotient_eq :
    gammaEnergy 0 (fun t => jetProfile 1 t - jetProfile (4 * 1) t) /
      gammaEnergy 0 (fun t => jetProfile 1 t + jetProfile (2 * 1) t) = dyadicQuotient := by
  have h1 := gammaEnergy_dyadic_telescoped one_pos
  have h2 := gammaEnergy_dyadic_pair one_pos
  have hG : Real.Gamma 5 ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  unfold dyadicQuotient
  rw [one_mul] at h1 h2
  rw [← h1, ← h2]
  field_simp

/-- The diagonal scale `ε_j = 1/(j+2)`. -/
def diagScale (j : ℕ) : ℝ := 1 / ((j : ℝ) + 2)

theorem diagScale_pos (j : ℕ) : 0 < diagScale j := by unfold diagScale; positivity

theorem diagScale_le (j : ℕ) : diagScale j ≤ 1 / 2 := by
  unfold diagScale
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem tendsto_diagScale : Tendsto diagScale atTop (𝓝 0) := by
  refine squeeze_zero (fun j => (diagScale_pos j).le) (fun j => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  unfold diagScale
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Admissible diagonal prime quadruples at scale `ε`. -/
def DyadicQuadruple (ε : ℝ) (r₀ r₁ p₀ p₁ : ℕ) : Prop :=
  r₀.Prime ∧ r₁.Prime ∧ p₀.Prime ∧ p₁.Prime ∧ 6 < r₀ ∧
    (2 * r₀ : ℝ) < r₁ ∧ (r₁ : ℝ) < (1 + ε ^ 2) * (2 * r₀) ∧
    (1 + ε) * (3 * r₀) < (p₀ : ℝ) ∧ (p₀ : ℝ) < (1 + ε ^ 2) * ((1 + ε) * (3 * r₀)) ∧
    (1 + ε) * (3 * r₁) < (p₁ : ℝ) ∧ (p₁ : ℝ) < (1 + ε ^ 2) * ((1 + ε) * (3 * r₁))

theorem exists_dyadicQuadruple {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ r₀ r₁ p₀ p₁ : ℕ, n ≤ r₀ ∧ DyadicQuadruple ε r₀ r₁ p₀ p₁ := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (prime_between (ε := ε ^ 2) (by positivity))
  obtain ⟨r₀, hr₀n, hr₀⟩ := Nat.exists_infinite_primes (max (max n 7) ⌈X⌉₊)
  have hXr : X ≤ (r₀ : ℝ) := by
    have h1 : (⌈X⌉₊ : ℝ) ≤ r₀ := by exact_mod_cast (le_max_right _ _).trans hr₀n
    exact (Nat.le_ceil X).trans h1
  have hr0pos : (0 : ℝ) ≤ r₀ := Nat.cast_nonneg _
  obtain ⟨r₁, hr₁, hlo1, hhi1⟩ := hX (2 * r₀) (by linarith)
  obtain ⟨p₀, hp₀, hlo2, hhi2⟩ := hX ((1 + ε) * (3 * r₀)) (by nlinarith)
  have hr1pos : (2 * r₀ : ℝ) < r₁ := hlo1
  obtain ⟨p₁, hp₁, hlo3, hhi3⟩ := hX ((1 + ε) * (3 * r₁)) (by nlinarith)
  refine ⟨r₀, r₁, p₀, p₁, (le_max_left _ _).trans ((le_max_left _ _).trans hr₀n),
    hr₀, hr₁, hp₀, hp₁, ?_, hlo1, hhi1, hlo2, hhi2, hlo3, hhi3⟩
  have := (le_max_right _ _).trans ((le_max_left _ _).trans hr₀n)
  omega

private theorem dyadic_scalar_bound {C₁ C₂ ε e₀ e₁ y u P : ℝ} (hC1 : 0 ≤ C₁) (hC2 : 0 ≤ C₂)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (he0 : ε ≤ e₀) (he0' : e₀ ≤ ε + ε ^ 2 + ε ^ 3)
    (he1 : ε ≤ e₁) (he1' : e₁ ≤ ε + ε ^ 2 + ε ^ 3) (hy : 2 ≤ y) (hy' : y ≤ 2 + 2 * ε ^ 2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    (2 * C₂ * 1 * e₀ ^ 2 / ε + |1 - e₀ / ε| * (C₁ * 1)) +
      (2 * C₂ * u * e₁ ^ 2 / ε + |1 - e₁ / ε| * (C₁ * u) +
        (y - 2) * (C₁ * y ^ 2 * P / 2 + C₂ * y ^ 2 * P / 2 ^ 2 * 2)) ≤
      (22 * C₁ + 52 * C₂) * ε := by
  have hε2' : ε ^ 2 ≤ ε / 2 := by nlinarith
  have hε3 : ε ^ 3 ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]
  have hq : ∀ e, ε ≤ e → e ≤ ε + ε ^ 2 + ε ^ 3 → |1 - e / ε| ≤ 2 * ε := by
    intro e h1 h2
    rw [abs_sub_comm, abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hε]; linarith)]
    rw [sub_le_iff_le_add, div_le_iff₀ hε]; nlinarith
  have hsq : ∀ e, ε ≤ e → e ≤ ε + ε ^ 2 + ε ^ 3 → e ^ 2 / ε ≤ 4 * ε := by
    intro e h1 h2
    rw [div_le_iff₀ hε]; nlinarith
  have q0 := hq e₀ he0 he0'
  have q1 := hq e₁ he1 he1'
  have s0 := hsq e₀ he0 he0'
  have s1 := hsq e₁ he1 he1'
  have t1 : 2 * C₂ * 1 * e₀ ^ 2 / ε = 2 * C₂ * (e₀ ^ 2 / ε) := by ring
  have t2 : 2 * C₂ * u * e₁ ^ 2 / ε = 2 * C₂ * u * (e₁ ^ 2 / ε) := by ring
  rw [t1, t2]
  have a1 : 2 * C₂ * (e₀ ^ 2 / ε) ≤ 8 * C₂ * ε := by nlinarith
  have a2 : |1 - e₀ / ε| * (C₁ * 1) ≤ 2 * C₁ * ε := by nlinarith [abs_nonneg (1 - e₀ / ε)]
  have a3 : 2 * C₂ * u * (e₁ ^ 2 / ε) ≤ 8 * C₂ * ε := by
    have : 0 ≤ e₁ ^ 2 / ε := by positivity
    have h := mul_le_mul hu1 s1 this zero_le_one
    nlinarith
  have a4 : |1 - e₁ / ε| * (C₁ * u) ≤ 2 * C₁ * ε := by
    have h := mul_le_mul q1 (mul_le_mul_of_nonneg_left hu1 hC1) (by positivity) (by positivity)
    nlinarith
  have hy2 : y ^ 2 * P ≤ 9 := by
    have : y ^ 2 ≤ 9 := by nlinarith
    nlinarith
  have hbr : C₁ * y ^ 2 * P / 2 + C₂ * y ^ 2 * P / 2 ^ 2 * 2 = (C₁ + C₂) / 2 * (y ^ 2 * P) := by
    ring
  have a5 : (y - 2) * (C₁ * y ^ 2 * P / 2 + C₂ * y ^ 2 * P / 2 ^ 2 * 2) ≤
      (18 * C₁ + 36 * C₂) * ε := by
    rw [hbr]
    have h1 : (C₁ + C₂) / 2 * (y ^ 2 * P) ≤ (C₁ + C₂) / 2 * 9 :=
      mul_le_mul_of_nonneg_left hy2 (by positivity)
    have h2 : (y - 2) * ((C₁ + C₂) / 2 * (y ^ 2 * P)) ≤ (2 * ε ^ 2) * ((C₁ + C₂) / 2 * 9) :=
      mul_le_mul (by linarith) h1 (by positivity) (by positivity)
    nlinarith
  linarith

/-- A uniform first-jet approximation of the rescaled diagonal precursor at `δ = 0`. -/
theorem exists_dyadic_approx_const :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε e₀ e₁ y : ℝ, 0 < ε → ε ≤ 1 / 2 → ε ≤ e₀ → e₀ ≤ ε + ε ^ 2 + ε ^ 3 →
      ε ≤ e₁ → e₁ ≤ ε + ε ^ 2 + ε ^ 3 → 2 ≤ y → y ≤ 2 + 2 * ε ^ 2 →
      gammaNorm 0 (fun t => twoDipolePrecursor 1 (1 + e₀) y (y * (1 + e₁)) t / ε +
        (jetProfile 1 t + jetProfile 2 t)) ≤ K * ε := by
  have hC1 := jetConst_nonneg 1
  have hC2 := jetConst_nonneg 2
  refine ⟨22 * jetConst 1 + 52 * jetConst 2, by positivity, ?_⟩
  intro ε e₀ e₁ y hε hε2 he0 he0' he1 he1' hy hy'
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hy0 : 0 < y := by linarith
  have e : (fun t => twoDipolePrecursor 1 (1 + e₀) y (y * (1 + e₁)) t / ε +
      (jetProfile 1 t + jetProfile 2 t)) =
      fun t => ((atom 1 t - atom (1 * (1 + e₀)) t) / ε + jetProfile 1 t) +
        ((atom y t - atom (y * (1 + e₁)) t) / ε + jetProfile 2 t) := by
    funext t; unfold twoDipolePrecursor; rw [one_mul]; ring
  have f1 : GammaFinite 0 (fun t => (atom 1 t - atom (1 * (1 + e₀)) t) / ε + jetProfile 1 t) := by
    have := (((gammaFinite_atom hδ one_pos).sub (gammaFinite_atom hδ
      (by nlinarith : (0:ℝ) < 1 * (1 + e₀)))).smul ε⁻¹).add (gammaFinite_jetProfile hδ one_pos)
    refine this.congr ?_; funext t; ring
  have f2 : GammaFinite 0 (fun t => (atom y t - atom (y * (1 + e₁)) t) / ε + jetProfile 2 t) := by
    have := (((gammaFinite_atom hδ hy0).sub (gammaFinite_atom hδ
      (by nlinarith : (0:ℝ) < y * (1 + e₁)))).smul ε⁻¹).add (gammaFinite_jetProfile hδ two_pos)
    refine this.congr ?_; funext t; ring
  rw [e]
  refine (gammaNorm_add_le hδ f1 f2).trans ?_
  have b1 := gammaNorm_dipole_div_add_le (δ := 0) le_rfl zero_le_one (x := 1) (y := 1) (e := e₀)
    one_pos le_rfl (by linarith) (by nlinarith) hε
  have b2 := gammaNorm_dipole_div_add_le (δ := 0) le_rfl zero_le_one (x := 2) (y := y) (e := e₁)
    two_pos hy (by linarith) (by nlinarith) hε
  have hpow1 : (1 : ℝ) ^ (-(1 + 0 : ℝ) / 2) = 1 := Real.one_rpow _
  rw [hpow1, sub_self, zero_mul, add_zero] at b1
  have hu1 : y ^ (-(1 + 0 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hu0 : 0 ≤ y ^ (-(1 + 0 : ℝ) / 2) := by positivity
  have hP1 : ((2 : ℝ) ^ ((5 + 0 : ℝ) / 2))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  have hP0 : 0 ≤ ((2 : ℝ) ^ ((5 + 0 : ℝ) / 2))⁻¹ := by positivity
  have hb := dyadic_scalar_bound hC1 hC2 hε hε2 he0 he0' he1 he1' hy hy' hu0 hu1 hP0 hP1
  have e2 : (2 : ℝ) ^ 2 = 2 ^ 2 := rfl
  linarith

/-- **The literal positive dyadic mechanism.**  With `ε_j = 1/(j+2)` there are primes
`r₀ < r₁`, `p₀`, `p₁` with `r₁/(2r₀) ∈ (1, 1+ε²)` and `p_k/(3r_k) ∈ (1+ε, (1+ε²)(1+ε))`; the
precursor `f_(3r₀) - f_(p₀) + f_(3r₁) - f_(p₁)` and its `2`-inserted eight-atom packet carry
literal Möbius signs on eight distinct atoms, and their `δ = 0` energy ratio tends to the quotient
of card equation (5), which is `< 4/5`. -/
theorem exists_dyadic_realization :
    ∃ r₀ r₁ p₀ p₁ : ℕ → ℕ,
      (∀ j, j ≤ r₀ j ∧ DyadicQuadruple (diagScale j) (r₀ j) (r₁ j) (p₀ j) (p₁ j)) ∧
      (∀ j, μ (3 * r₀ j) = 1 ∧ μ (p₀ j) = -1 ∧ μ (3 * r₁ j) = 1 ∧ μ (p₁ j) = -1 ∧
        μ (6 * r₀ j) = -1 ∧ μ (2 * p₀ j) = 1 ∧ μ (6 * r₁ j) = -1 ∧ μ (2 * p₁ j) = 1) ∧
      (∀ j, [3 * r₀ j, p₀ j, 6 * r₀ j, 2 * p₀ j, 3 * r₁ j, p₁ j, 6 * r₁ j, 2 * p₁ j].Nodup) ∧
      Tendsto (fun j =>
        gammaEnergy 0 (insertTwo (twoDipolePrecursor (3 * r₀ j) (p₀ j) (3 * r₁ j) (p₁ j))) /
          gammaEnergy 0 (twoDipolePrecursor (3 * r₀ j) (p₀ j) (3 * r₁ j) (p₁ j)))
        atTop (𝓝 dyadicQuotient) ∧
      dyadicQuotient < 4 / 5 := by
  have hq : ∀ j : ℕ, ∃ q : ℕ × ℕ × ℕ × ℕ, j ≤ q.1 ∧
      DyadicQuadruple (diagScale j) q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    intro j
    obtain ⟨r₀, r₁, p₀, p₁, h1, h2⟩ := exists_dyadicQuadruple (diagScale_pos j) j
    exact ⟨(r₀, r₁, p₀, p₁), h1, h2⟩
  choose q hq using hq
  set r₀ : ℕ → ℕ := fun j => (q j).1
  set r₁ : ℕ → ℕ := fun j => (q j).2.1
  set p₀ : ℕ → ℕ := fun j => (q j).2.2.1
  set p₁ : ℕ → ℕ := fun j => (q j).2.2.2
  -- real-number facts at each index
  have hfacts : ∀ j, let ε := diagScale j
      (6 : ℝ) < r₀ j ∧ (2 * r₀ j : ℝ) < r₁ j ∧ (r₁ j : ℝ) < (1 + ε ^ 2) * (2 * r₀ j) ∧
      (1 + ε) * (3 * r₀ j) < (p₀ j : ℝ) ∧ (p₀ j : ℝ) < (1 + ε ^ 2) * ((1 + ε) * (3 * r₀ j)) ∧
      (1 + ε) * (3 * r₁ j) < (p₁ j : ℝ) ∧ (p₁ j : ℝ) < (1 + ε ^ 2) * ((1 + ε) * (3 * r₁ j)) := by
    intro j
    obtain ⟨-, -, -, -, -, h6, a, b, c, d, e, f⟩ := hq j
    exact ⟨by exact_mod_cast h6, a, b, c, d, e, f⟩
  refine ⟨r₀, r₁, p₀, p₁, hq, fun j => ?_, fun j => ?_, ?_, dyadicQuotient_lt⟩
  · obtain ⟨-, ⟨hr₀, hr₁, hp₀, hp₁, h6, -⟩⟩ := hq j
    obtain ⟨-, a, -, c, -, e, -⟩ := hfacts j
    have h6 : 6 < r₀ j := h6
    have hε := diagScale_pos j
    have a' : 2 * r₀ j < r₁ j := by exact_mod_cast a
    have c' : 3 * r₀ j < p₀ j := by
      have : (3 * r₀ j : ℝ) < p₀ j := by nlinarith
      exact_mod_cast this
    have e' : 3 * r₁ j < p₁ j := by
      have : (3 * r₁ j : ℝ) < p₁ j := by nlinarith
      exact_mod_cast this
    exact ⟨moebius_three_mul hr₀ (by omega), moebius_prime _ hp₀, moebius_three_mul hr₁ (by omega),
      moebius_prime _ hp₁, moebius_six_mul hr₀ h6, moebius_two_mul hp₀ (by omega),
      moebius_six_mul hr₁ (by omega), moebius_two_mul hp₁ (by omega)⟩
  · obtain ⟨-, ⟨-, -, -, hp₁, h6, -⟩⟩ := hq j
    obtain ⟨-, a, b, c, d, e, f⟩ := hfacts j
    have h6 : 6 < r₀ j := h6
    have hε := diagScale_pos j
    have hε2 := diagScale_le j
    have hr0 : (0 : ℝ) < r₀ j := by exact_mod_cast (by omega : 0 < r₀ j)
    have hr1 : (0 : ℝ) < r₁ j := by linarith
    have k1 : (1 + diagScale j ^ 2) * (1 + diagScale j) ≤ 15 / 8 := by nlinarith
    have n1 : 3 * r₀ j < p₀ j := by
      have : (3 * r₀ j : ℝ) < p₀ j := by nlinarith
      exact_mod_cast this
    have n2 : p₀ j < 6 * r₀ j := by
      have : (p₀ j : ℝ) < 6 * r₀ j := by nlinarith
      exact_mod_cast this
    have n3 : 2 * r₀ j < r₁ j := by exact_mod_cast a
    have n4 : 3 * r₁ j < 2 * p₀ j := by
      have : (3 * r₁ j : ℝ) < 2 * p₀ j := by nlinarith
      exact_mod_cast this
    have n5 : 3 * r₁ j < p₁ j := by
      have : (3 * r₁ j : ℝ) < p₁ j := by nlinarith
      exact_mod_cast this
    have n6 : p₁ j < 6 * r₁ j := by
      have : (p₁ j : ℝ) < 6 * r₁ j := by nlinarith
      exact_mod_cast this
    have n7 : 2 * p₀ j < 6 * r₁ j := by omega
    have hodd : p₁ j % 2 = 1 := by
      rcases hp₁.eq_two_or_odd with h | h
      · omega
      · exact h
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or]
    omega
  · -- the energy ratio
    have hδ : (0 : ℝ) < 5 + 0 := by norm_num
    obtain ⟨K, hK0, hK⟩ := exists_dyadic_approx_const
    set ε : ℕ → ℝ := diagScale with hε_def
    set X : ℕ → ℝ := fun j => 3 * (r₀ j : ℝ) with hX
    set e₀ : ℕ → ℝ := fun j => (p₀ j : ℝ) / X j - 1 with he₀
    set y : ℕ → ℝ := fun j => (r₁ j : ℝ) / r₀ j with hy
    set e₁ : ℕ → ℝ := fun j => (p₁ j : ℝ) / (3 * r₁ j) - 1 with he₁
    set Bt : ℕ → ℝ → ℝ := fun j => twoDipolePrecursor 1 (1 + e₀ j) (y j) (y j * (1 + e₁ j))
      with hBt
    have hpos : ∀ j, (0 : ℝ) < r₀ j := fun j => by
      obtain ⟨h6, -⟩ := hfacts j; linarith
    have hscale : ∀ j, twoDipolePrecursor (3 * r₀ j : ℕ) (p₀ j) (3 * r₁ j : ℕ) (p₁ j) =
        dilate (X j) (Bt j) := by
      intro j
      have hr0 := hpos j
      obtain ⟨-, a, -, -, -, -, -⟩ := hfacts j
      have hr1 : (0 : ℝ) < r₁ j := by linarith
      rw [hBt, ← twoDipolePrecursor_scale]
      congr 1
      · simp [hX]
      · simp only [he₀, hX]; field_simp
      · simp only [hy, hX]; push_cast; field_simp
      · simp only [hy, he₁, hX]; push_cast; field_simp
    have hbounds : ∀ j, ε j ≤ e₀ j ∧ e₀ j ≤ ε j + ε j ^ 2 + ε j ^ 3 ∧ ε j ≤ e₁ j ∧
        e₁ j ≤ ε j + ε j ^ 2 + ε j ^ 3 ∧ 2 ≤ y j ∧ y j ≤ 2 + 2 * ε j ^ 2 := by
      intro j
      have hr0 := hpos j
      obtain ⟨-, a, b, c, d, e, f⟩ := hfacts j
      have hr1 : (0 : ℝ) < r₁ j := by linarith
      have hX0 : 0 < X j := by simp only [hX]; positivity
      simp only [he₀, he₁, hy, hε_def]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [le_sub_iff_add_le, le_div_iff₀ hX0]; simp only [hX]; linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hX0]; simp only [hX]; nlinarith
      · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]; linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
      · rw [le_div_iff₀ hr0]; linarith
      · rw [div_le_iff₀ hr0]; nlinarith
    have hBt_fin : ∀ j, GammaFinite 0 (Bt j) := by
      intro j
      obtain ⟨h1, -, h3, -, h5, -⟩ := hbounds j
      have := diagScale_pos j
      exact gammaFinite_twoDipolePrecursor hδ one_pos (by nlinarith) (by linarith) (by nlinarith)
    set V : ℝ → ℝ := fun t => jetProfile 1 t + jetProfile 2 t with hV
    have hVfin : GammaFinite 0 V := (gammaFinite_jetProfile hδ one_pos).add
      (gammaFinite_jetProfile hδ two_pos)
    have happrox : ∀ j, gammaNorm 0 (fun t => Bt j t / ε j + V t) ≤ K * ε j := by
      intro j
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbounds j
      exact hK (ε j) (e₀ j) (e₁ j) (y j) (diagScale_pos j) (diagScale_le j) h1 h2 h3 h4 h5 h6
    have hlimB : Tendsto (fun j => gammaNorm 0 (fun t => Bt j t / ε j + V t)) atTop (𝓝 0) := by
      have := tendsto_diagScale.const_mul K
      rw [mul_zero] at this
      exact squeeze_zero (fun j => gammaNorm_nonneg _ _) happrox this
    have hlimI : Tendsto (fun j => gammaNorm 0 (fun t => insertTwo (Bt j) t / ε j +
        insertTwo V t)) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => gammaNorm_nonneg _ _) (fun j => ?_) (by
        have := hlimB.const_mul 2; rwa [mul_zero] at this)
      have e : (fun t => insertTwo (Bt j) t / ε j + insertTwo V t) =
          insertTwo (fun t => Bt j t / ε j + V t) := by
        funext t; unfold insertTwo dilate; ring
      rw [e]
      exact gammaNorm_insertTwo_le le_rfl (((hBt_fin j).smul (ε j)⁻¹).add hVfin |>.congr
        (by funext t; ring))
    have hEB := tendsto_gammaEnergy_div_sq_seq hδ (fun j => diagScale_pos j) hBt_fin hVfin hlimB
    have hEI := tendsto_gammaEnergy_div_sq_seq hδ (fun j => diagScale_pos j)
      (fun j => gammaFinite_insertTwo (hBt_fin j)) (gammaFinite_insertTwo hVfin) hlimI
    have hIV : insertTwo V = fun t => jetProfile 1 t - jetProfile (4 * 1) t := by
      funext t
      have := dyadic_insertion_telescopes 1 t
      unfold insertTwo
      rw [hV]
      simpa [mul_one] using this
    rw [hIV] at hEI
    have hV' : V = fun t => jetProfile 1 t + jetProfile (2 * 1) t := by
      funext t; simp [hV]
    rw [hV'] at hEB
    have hpos0 : gammaEnergy 0 (fun t => jetProfile 1 t + jetProfile (2 * 1) t) ≠ 0 := by
      have h := gammaEnergy_dyadic_pair (x := 1) one_pos
      intro h0
      rw [h0, mul_zero] at h
      norm_num at h
    have hlim := hEI.div hEB hpos0
    rw [dyadicQuotient_eq] at hlim
    refine hlim.congr fun j => ?_
    have hX0 : 0 < X j := by simp only [hX]; have := hpos j; positivity
    have he : ε j ^ 2 ≠ 0 := by have := diagScale_pos j; positivity
    simp only [Pi.div_apply]
    push_cast
    rw [hscale j, insertTwo_dilate, gammaEnergy_dilate hX0, gammaEnergy_dilate hX0]
    have hXp : X j ^ (-1 - (0 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hX0 _).ne'
    by_cases h0 : gammaEnergy 0 (Bt j) = 0
    · rw [h0]; simp
    · field_simp

end RHTower.CubicGamma
