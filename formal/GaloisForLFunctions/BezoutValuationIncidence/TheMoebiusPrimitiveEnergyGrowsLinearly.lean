import GaloisForLFunctions.BezoutValuationIncidence.MoebiusPrimitiveFibreMasses

/-!
# The Möbius primitive energy grows linearly

The complete-period energy of the centred Möbius discrepancy grows exactly linearly
(`tendsto_twelve_mul_sievePrimitiveEnergy_moebius_div`):

`12 E_prim(N; μ)/N → c = Σ_{j ≥ 1} T(j)/(j(j+1))`,  `T(j) = Σ_{a,b ≤ j} μ(a)μ(b) δ([a,b])/(ab)`,

with `δ(m)` the density of `μ(q)² J₂(q)/q² [(q,m)=1]` (`jordanCoprimeDensity`); numerically
`c ≈ 0.3311`. The bounds `N/2 ≤ 3456 E_prim(N; μ)` and `12 E_prim(N; μ) ≤ 64 N (1 + log N)` left the
order between `N` and `N log N`: the period discrepancy of the Möbius row is diffusive, with an
explicit diffusion constant.

Mechanism. The Jordan spectrum is `12 E = Σ_q μ(q)² (J₂(q)/q²) m_q(⌊N/q⌋)²`
(`twelve_mul_sievePrimitiveEnergy_moebius_eq`). On the fibre `⌊N/q⌋ = j`,
`m_q(j)² = Σ_{a,b ≤ j} μ(a)μ(b)/(ab) [(q,[a,b])=1]`, so the fibre is a combination of Jordan fibre
masses (`sum_fibre_jordan_eq`), which equidistribute (`abs_jordanFibreMass_sub_le`): fibre `j`
carries `N T(j)/(j(j+1))` up to `O(j² √N log N)`. The fibres `j > J = ⌊N^{1/16}⌋` hold the modes
`q ≤ N/J`, where `|m_q| ≤ q/φ(q)` and `Σ_{q ≤ x} (q/φ(q))³ ≪ x` give `O(N/J)`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have ha0 := ha.ne_zero
  have hb0 := hb.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha0 hb0)]
  intro p
  rw [Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply]
  exact sup_le ((Nat.squarefree_iff_factorization_le_one ha0).mp ha p)
    ((Nat.squarefree_iff_factorization_le_one hb0).mp hb p)

theorem coprime_lcm_iff {q a b : ℕ} :
    Nat.Coprime q (Nat.lcm a b) ↔ Nat.Coprime a q ∧ Nat.Coprime b q := by
  constructor
  · intro h
    exact ⟨(h.coprime_dvd_right (Nat.dvd_lcm_left a b)).symm,
      (h.coprime_dvd_right (Nat.dvd_lcm_right a b)).symm⟩
  · rintro ⟨ha, hb⟩
    exact (Nat.Coprime.mul_right ha.symm hb.symm).coprime_dvd_right
      (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))

/-! ### The Jordan spectrum in fibres -/

/-- `12 E_prim(N; μ) = Σ_{2 ≤ q ≤ N} μ(q)² (J₂(q)/q²) m_q(⌊N/q⌋)²`. -/
theorem twelve_mul_sievePrimitiveEnergy_moebius_eq (N : ℕ) :
    12 * sievePrimitiveEnergy N moebiusReal = ∑ q ∈ Icc 2 N,
      (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
        coprimeHarmonicMoebius q (N / q) ^ 2 := by
  rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
  refine sum_congr rfl fun q _ => ?_
  rw [selbergMultiplesCoord_moebiusReal_sq]
  unfold moebiusReal
  ring

/-- `m_q(j)² = Σ_{a,b ≤ j} μ(a)μ(b)/(ab) [(q,[a,b])=1]`. -/
theorem coprimeHarmonicMoebius_sq_eq (q j : ℕ) :
    coprimeHarmonicMoebius q j ^ 2 = ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j,
      if Nat.Coprime q (Nat.lcm a b) then (moebius a : ℝ) * moebius b / ((a : ℝ) * b) else 0 := by
  unfold coprimeHarmonicMoebius
  rw [sq, sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  unfold moebiusReal
  by_cases ha : Nat.Coprime a q <;> by_cases hb : Nat.Coprime b q
  · rw [if_pos ha, if_pos hb, if_pos (coprime_lcm_iff.mpr ⟨ha, hb⟩)]; ring
  · rw [if_pos ha, if_neg hb, if_neg (fun h => hb (coprime_lcm_iff.mp h).2), mul_zero]
  · rw [if_neg ha, if_neg (fun h => ha (coprime_lcm_iff.mp h).1), zero_mul]
  · rw [if_neg ha, if_neg (fun h => ha (coprime_lcm_iff.mp h).1), zero_mul]

/-- **Fibre identity.** The fibre `⌊N/q⌋ = j` of the Jordan spectrum is
`Σ_{a,b ≤ j} μ(a)μ(b)/(ab) U_{[a,b]}(N,j)`. -/
theorem sum_fibre_jordan_eq (N j : ℕ) :
    ∑ q ∈ (Icc 1 N).filter (fun q => N / q = j),
        (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
          coprimeHarmonicMoebius q j ^ 2 =
      ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j, (moebius a : ℝ) * moebius b / ((a : ℝ) * b) *
        jordanFibreMass (Nat.lcm a b) N j := by
  simp only [coprimeHarmonicMoebius_sq_eq, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  unfold jordanFibreMass
  rw [mul_sum]
  refine sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

/-- `T(j) = Σ_{a,b ≤ j} μ(a)μ(b) δ([a,b])/(ab)`. -/
def primitiveFibreWeight (j : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j,
    (moebius a : ℝ) * moebius b * jordanCoprimeDensity (Nat.lcm a b) / ((a : ℝ) * b)

/-- **Fibre law.** For `j, N ≥ 1` the fibre `⌊N/q⌋ = j` carries `N T(j)/(j(j+1))` up to
`j² (2 ζ(3/2) √N (2 + ζ(3/2) + log N) + 3 ζ(2))`. -/
theorem abs_sum_fibre_jordan_sub_le {N j : ℕ} (hj : 1 ≤ j) (hN : 1 ≤ N) :
    |∑ q ∈ (Icc 1 N).filter (fun q => N / q = j),
        (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
          coprimeHarmonicMoebius q j ^ 2 - N * primitiveFibreWeight j / ((j : ℝ) * (j + 1))| ≤
      (j : ℝ) ^ 2 * (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
          (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
        3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  have hZ0 : 0 ≤ ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hZ20 : 0 ≤ ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := tsum_nonneg fun i => by positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hjj : (0 : ℝ) < (j : ℝ) * (j + 1) := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    positivity
  have hT : (N : ℝ) * primitiveFibreWeight j / ((j : ℝ) * (j + 1)) =
      ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j, (moebius a : ℝ) * moebius b / ((a : ℝ) * b) *
        (jordanCoprimeDensity (Nat.lcm a b) * N / ((j : ℝ) * (j + 1))) := by
    unfold primitiveFibreWeight
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, sum_div]
    exact sum_congr rfl fun b _ => by ring
  have hpt : ∀ a ∈ Icc 1 j, ∀ b ∈ Icc 1 j,
      |(moebius a : ℝ) * moebius b / ((a : ℝ) * b) * jordanFibreMass (Nat.lcm a b) N j -
        (moebius a : ℝ) * moebius b / ((a : ℝ) * b) *
          (jordanCoprimeDensity (Nat.lcm a b) * N / ((j : ℝ) * (j + 1)))| ≤
      2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
          (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
        3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro a ha b hb
    have ha1 := (mem_Icc.mp ha).1
    have hb1 := (mem_Icc.mp hb).1
    have hab0 : (0 : ℝ) < (a : ℝ) * b := by
      have h1 : (0 : ℝ) < a := by exact_mod_cast ha1
      have h2 : (0 : ℝ) < b := by exact_mod_cast hb1
      positivity
    have hR0 : 0 ≤ 2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
        (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
        3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
      add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hZ0) (Real.sqrt_nonneg _))
        (by linarith)) (mul_nonneg (by norm_num) hZ20)
    rw [← mul_sub, abs_mul]
    by_cases hsq : Squarefree a ∧ Squarefree b
    · have hl := squarefree_lcm hsq.1 hsq.2
      have hU := abs_jordanFibreMass_sub_le hl hj hN
      have hτ : ((Nat.lcm a b).divisors.card : ℝ) ≤ (a : ℝ) * b := by
        have h1 := Nat.card_divisors_le_self (Nat.lcm a b)
        have h2 : Nat.lcm a b ≤ a * b :=
          Nat.le_of_dvd (Nat.mul_pos ha1 hb1) (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
        have : (Nat.lcm a b).divisors.card ≤ a * b := h1.trans h2
        exact_mod_cast this
      have hμ : |(moebius a : ℝ) * moebius b / ((a : ℝ) * b)| ≤ ((a : ℝ) * b)⁻¹ := by
        rw [abs_div, abs_of_pos hab0, div_eq_mul_inv]
        apply mul_le_of_le_one_left (inv_nonneg.mpr hab0.le)
        rw [abs_mul]
        have h1 : |(moebius a : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |(moebius b : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        nlinarith [abs_nonneg (moebius a : ℝ), abs_nonneg (moebius b : ℝ)]
      have hK0 : 0 ≤ 2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
          (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hZ0) (Real.sqrt_nonneg _)) (by linarith)
      have hab1 : (1 : ℝ) ≤ (a : ℝ) * b := by
        have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
        have h2 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
        nlinarith
      have hinv1 : ((a : ℝ) * b)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hab1
      calc |(moebius a : ℝ) * moebius b / ((a : ℝ) * b)| *
            |jordanFibreMass (Nat.lcm a b) N j -
              jordanCoprimeDensity (Nat.lcm a b) * N / ((j : ℝ) * (j + 1))|
          ≤ ((a : ℝ) * b)⁻¹ * (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) *
              ((Nat.lcm a b).divisors.card : ℝ) * Real.sqrt N *
              (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
              3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
            mul_le_mul hμ hU (abs_nonneg _) (inv_nonneg.mpr hab0.le)
        _ = ((a : ℝ) * b)⁻¹ * ((Nat.lcm a b).divisors.card : ℝ) *
              (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
                (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N)) +
            ((a : ℝ) * b)⁻¹ * (3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by ring
        _ ≤ 1 * (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
                (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N)) +
            1 * (3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
          have hr : ((a : ℝ) * b)⁻¹ * ((Nat.lcm a b).divisors.card : ℝ) ≤ 1 := by
            rw [inv_mul_le_iff₀ hab0, mul_one]; exact hτ
          exact add_le_add (mul_le_mul_of_nonneg_right hr hK0)
            (mul_le_mul_of_nonneg_right hinv1 (mul_nonneg (by norm_num) hZ20))
        _ = _ := by ring
    · have h0 : (moebius a : ℝ) * moebius b = 0 := by
        rcases not_and_or.mp hsq with h | h
        · rw [moebius_eq_zero_of_not_squarefree h]; simp
        · rw [moebius_eq_zero_of_not_squarefree h]; simp
      rw [h0, zero_div, abs_zero, zero_mul]
      exact hR0
  rw [sum_fibre_jordan_eq, hT]
  calc _ ≤ ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j,
        |(moebius a : ℝ) * moebius b / ((a : ℝ) * b) * jordanFibreMass (Nat.lcm a b) N j -
          (moebius a : ℝ) * moebius b / ((a : ℝ) * b) *
            (jordanCoprimeDensity (Nat.lcm a b) * N / ((j : ℝ) * (j + 1)))| := by
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
        rw [← sum_sub_distrib]
        exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j,
        (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
          (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
        3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => hpt a ha b hb
    _ = _ := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

/-! ### Splitting at the fibre cutoff -/

/-- `12 E = Σ_{j ≤ J} (fibre j) + Σ_{⌊N/q⌋ > J} (mode q)` for `J < N`. -/
theorem twelve_mul_sievePrimitiveEnergy_moebius_split {N J : ℕ} (hJN : J < N) :
    12 * sievePrimitiveEnergy N moebiusReal =
      ∑ j ∈ Icc 1 J, ∑ q ∈ (Icc 1 N).filter (fun q => N / q = j),
          (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
            coprimeHarmonicMoebius q j ^ 2 +
        ∑ q ∈ (Icc 2 N).filter (fun q => ¬ N / q ≤ J),
          (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
            coprimeHarmonicMoebius q (N / q) ^ 2 := by
  rw [twelve_mul_sievePrimitiveEnergy_moebius_eq,
    ← sum_filter_add_sum_filter_not (Icc 2 N) (fun q => N / q ≤ J)]
  congr 1
  rw [← sum_fiberwise_of_maps_to (s := (Icc 2 N).filter (fun q => N / q ≤ J)) (t := Icc 1 J)
    (g := fun q => N / q) (fun q hq => by
      obtain ⟨hqI, hqJ⟩ := mem_filter.mp hq
      obtain ⟨hq2, hqN⟩ := mem_Icc.mp hqI
      exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr hqN, hqJ⟩)]
  refine sum_congr rfl fun j hj => ?_
  have hjJ := (mem_Icc.mp hj).2
  rw [filter_filter]
  refine sum_congr (by
    ext q
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h2, hN⟩, -, h⟩; exact ⟨⟨by omega, hN⟩, h⟩
    · rintro ⟨⟨h1, hN⟩, h⟩
      have hq1 : q ≠ 1 := by
        rintro rfl
        rw [Nat.div_one] at h
        omega
      exact ⟨⟨by omega, hN⟩, by rw [h]; exact hjJ, h⟩) fun q hq => ?_
  rw [(mem_filter.mp hq).2]

/-- **Tail.** The modes with `⌊N/q⌋ > J` carry at most `e^{19/2} ⌊N/(J+1)⌋`. -/
theorem sum_jordan_tail_le (N J : ℕ) :
    ∑ q ∈ (Icc 2 N).filter (fun q => ¬ N / q ≤ J),
        (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
          coprimeHarmonicMoebius q (N / q) ^ 2 ≤
      Real.exp (19 / 2) * ((N / (J + 1) : ℕ) : ℝ) := by
  have hpt : ∀ q ∈ (Icc 2 N).filter (fun q => ¬ N / q ≤ J),
      (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
          coprimeHarmonicMoebius q (N / q) ^ 2 ≤ ((q : ℝ) / (q.totient : ℝ)) ^ 3 := by
    intro q hq
    have hq2 := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hr1 : 1 ≤ (q : ℝ) / (q.totient : ℝ) := by rw [le_div_iff₀ hφ0, one_mul]; exact hφq
    have hJ0 := jordanTotient2_nonneg q
    have hJ1 : BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact jordanTotient2_le_sq q
    by_cases hsq : Squarefree q
    · have hμ : (moebius q : ℝ) ^ 2 = 1 := by
        have h1 : |(moebius q : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
        rw [← sq_abs, h1]; norm_num
      have hm := abs_coprimeHarmonicMoebius_le_ratio hsq (N / q)
      have hm2 : coprimeHarmonicMoebius q (N / q) ^ 2 ≤ ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hm 2
      rw [hμ, one_mul]
      calc BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2 * coprimeHarmonicMoebius q (N / q) ^ 2
          ≤ 1 * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := mul_le_mul hJ1 hm2 (sq_nonneg _) zero_le_one
        _ = ((q : ℝ) / (q.totient : ℝ)) ^ 2 * 1 := by ring
        _ ≤ ((q : ℝ) / (q.totient : ℝ)) ^ 2 * ((q : ℝ) / (q.totient : ℝ)) :=
            mul_le_mul_of_nonneg_left hr1 (sq_nonneg _)
        _ = ((q : ℝ) / (q.totient : ℝ)) ^ 3 := by ring
    · have hz : (moebius q : ℝ) = 0 := by rw [moebius_eq_zero_of_not_squarefree hsq]; simp
      rw [hz]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      positivity
  have hsub : (Icc 2 N).filter (fun q => ¬ N / q ≤ J) ⊆ Icc 1 (N / (J + 1)) := by
    intro q hq
    simp only [mem_filter, mem_Icc, not_le] at hq ⊢
    obtain ⟨⟨hq2, -⟩, hlt⟩ := hq
    refine ⟨by omega, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
    have := (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hlt
    linarith
  calc _ ≤ ∑ q ∈ (Icc 2 N).filter (fun q => ¬ N / q ≤ J), ((q : ℝ) / (q.totient : ℝ)) ^ 3 :=
        sum_le_sum hpt
    _ ≤ ∑ q ∈ Icc 1 (N / (J + 1)), ((q : ℝ) / (q.totient : ℝ)) ^ 3 :=
        sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => by positivity
    _ ≤ Real.exp (19 / 2) * ((N / (J + 1) : ℕ) : ℝ) := sum_div_totient_cube_le _

theorem sum_jordan_tail_nonneg (N J : ℕ) :
    0 ≤ ∑ q ∈ (Icc 2 N).filter (fun q => ¬ N / q ≤ J),
        (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
          coprimeHarmonicMoebius q (N / q) ^ 2 :=
  sum_nonneg fun q _ => mul_nonneg (mul_nonneg (sq_nonneg _)
    (div_nonneg (jordanTotient2_nonneg q) (sq_nonneg _))) (sq_nonneg _)

/-! ### The slope -/

theorem abs_primitiveFibreWeight_le (j : ℕ) :
    |primitiveFibreWeight j| ≤ (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (1 + Real.log j) ^ 2 := by
  have hZ30 : 0 ≤ ∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹ := tsum_nonneg fun d => by positivity
  have hpt : ∀ a ∈ Icc 1 j, ∀ b ∈ Icc 1 j,
      |(moebius a : ℝ) * moebius b * jordanCoprimeDensity (Nat.lcm a b) / ((a : ℝ) * b)| ≤
        (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (((a : ℝ))⁻¹ * ((b : ℝ))⁻¹) := by
    intro a ha b hb
    have h1 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
    have h2 : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
    have hμ : |(moebius a : ℝ) * moebius b| ≤ 1 := by
      rw [abs_mul]
      have h1 : |(moebius a : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have h2 : |(moebius b : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      nlinarith [abs_nonneg (moebius a : ℝ), abs_nonneg (moebius b : ℝ)]
    rw [abs_div, abs_mul, abs_of_pos (mul_pos h1 h2), div_eq_mul_inv, mul_inv]
    calc |(moebius a : ℝ) * moebius b| * |jordanCoprimeDensity (Nat.lcm a b)| *
          (((a : ℝ))⁻¹ * ((b : ℝ))⁻¹)
        ≤ 1 * (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (((a : ℝ))⁻¹ * ((b : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hμ (abs_jordanCoprimeDensity_le _)
            (abs_nonneg _) zero_le_one) (by positivity)
      _ = _ := by ring
  unfold primitiveFibreWeight
  calc _ ≤ ∑ a ∈ Icc 1 j, ∑ b ∈ Icc 1 j,
        (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (((a : ℝ))⁻¹ * ((b : ℝ))⁻¹) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a ha =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b hb => hpt a ha b hb))
    _ = (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * ((∑ a ∈ Icc 1 j, ((a : ℝ))⁻¹) *
          ∑ b ∈ Icc 1 j, ((b : ℝ))⁻¹) := by
        rw [sum_mul_sum, mul_sum]
        exact sum_congr rfl fun a _ => by rw [mul_sum]
    _ ≤ (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * ((1 + Real.log j) * (1 + Real.log j)) := by
        have hs := sum_inv_Icc_le j
        have hs0 : 0 ≤ ∑ a ∈ Icc 1 j, ((a : ℝ))⁻¹ := sum_nonneg fun a _ => by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul hs hs hs0 (by linarith)) hZ30
    _ = _ := by ring

theorem summable_primitiveFibreWeight_div :
    Summable (fun j : ℕ => primitiveFibreWeight j / ((j : ℝ) * (j + 1))) := by
  have hZ30 : 0 ≤ ∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹ := tsum_nonneg fun d => by positivity
  refine Summable.of_norm_bounded
    ((Real.summable_nat_rpow.mpr (by norm_num : -(7 / 4 : ℝ) < -1)).mul_left
      (64 * ∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹)) fun j => ?_
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [primitiveFibreWeight]
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hjj : (0 : ℝ) < (j : ℝ) * (j + 1) := by positivity
  rw [abs_div, abs_of_pos hjj, div_le_iff₀ hjj]
  have h1 := abs_primitiveFibreWeight_le j
  have h2 := one_add_log_sq_le_rpow_quarter hjR
  have h3 : (j : ℝ) ^ (1 / 4 : ℝ) = (j : ℝ) ^ (-(7 / 4 : ℝ)) * (j : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hj0]; norm_num
  have h4 : (j : ℝ) ^ 2 ≤ (j : ℝ) * (j + 1) := by nlinarith
  have hr0 : 0 ≤ (j : ℝ) ^ (-(7 / 4 : ℝ)) := Real.rpow_nonneg hj0.le _
  calc |primitiveFibreWeight j| ≤ (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (1 + Real.log j) ^ 2 := h1
    _ ≤ (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (64 * ((j : ℝ) ^ (-(7 / 4 : ℝ)) * (j : ℝ) ^ 2)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hZ30
    _ ≤ (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (64 * ((j : ℝ) ^ (-(7 / 4 : ℝ)) * ((j : ℝ) * (j + 1)))) := by
        gcongr
    _ = 64 * (∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹) * (j : ℝ) ^ (-(7 / 4 : ℝ)) * ((j : ℝ) * (j + 1)) := by
        ring

/-- The diffusion slope `c = Σ_{j ≥ 1} T(j)/(j(j+1))`. -/
def moebiusPrimitiveSlope : ℝ := ∑' j : ℕ, primitiveFibreWeight j / ((j : ℝ) * (j + 1))

theorem tendsto_sum_primitiveFibreWeight_div :
    Tendsto (fun J : ℕ => ∑ j ∈ Icc 1 J, primitiveFibreWeight j / ((j : ℝ) * (j + 1))) atTop
      (𝓝 moebiusPrimitiveSlope) := by
  have h := (summable_primitiveFibreWeight_div.hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun J => ?_
  simp only [Function.comp]
  have hset : range (J + 1) = insert 0 (Icc 1 J) := by
    ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hset, sum_insert (by simp)]
  simp [primitiveFibreWeight]

/-! ### The limit -/

/-- At cutoff `J` with `1 ≤ J < N`, `J¹⁶ ≤ N` and `log N ≤ 16 J`:
`|12 E/N − Σ_{j ≤ J} T(j)/(j(j+1))| ≤ (2ζ(3/2)(18 + ζ(3/2)) + 3ζ(2))/J⁴ + e^{19/2}/(J+1)`. -/
theorem abs_twelve_mul_div_sub_partial_le {N J : ℕ} (hJ1 : 1 ≤ J) (hJN : J < N)
    (hJ16 : J ^ 16 ≤ N) (hlog : Real.log N ≤ 16 * J) :
    |12 * sievePrimitiveEnergy N moebiusReal / N -
        ∑ j ∈ Icc 1 J, primitiveFibreWeight j / ((j : ℝ) * (j + 1))| ≤
      (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * (18 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) +
          3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) / (J : ℝ) ^ 4 +
        Real.exp (19 / 2) / ((J : ℝ) + 1) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hJ0 : (0 : ℝ) < J := by linarith
  have hfib : ∀ j ∈ Icc 1 J, |∑ q ∈ (Icc 1 N).filter (fun q => N / q = j),
      (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
        coprimeHarmonicMoebius q j ^ 2 - N * primitiveFibreWeight j / ((j : ℝ) * (j + 1))| ≤
      (J : ℝ) ^ 2 * (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * Real.sqrt N *
          (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
        3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := mem_Icc.mp hj
    refine (abs_sum_fibre_jordan_sub_le hj1 hN1).trans ?_
    have hZ0 : 0 ≤ ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) :=
      tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hZ20 : 0 ≤ ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := tsum_nonneg fun i => by positivity
    have hlN : 0 ≤ Real.log N := Real.log_nonneg hNR
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hjJ) 2
    · exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hZ0)
        (Real.sqrt_nonneg _)) (by linarith)) (mul_nonneg (by norm_num) hZ20)
  have hsplit := twelve_mul_sievePrimitiveEnergy_moebius_split hJN
  have htail := sum_jordan_tail_le N J
  have htail0 := sum_jordan_tail_nonneg N J
  have hZ0 : 0 ≤ ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hZ20 : 0 ≤ ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := tsum_nonneg fun i => by positivity
  generalize ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) = Z at hfib hZ0 ⊢
  generalize ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ = Z2 at hfib hZ20 ⊢
  -- the head error
  set A := ∑ j ∈ Icc 1 J, (∑ q ∈ (Icc 1 N).filter (fun q => N / q = j),
      (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
        coprimeHarmonicMoebius q j ^ 2 - N * primitiveFibreWeight j / ((j : ℝ) * (j + 1))) with hA
  set Tl := ∑ q ∈ (Icc 2 N).filter (fun q => ¬ N / q ≤ J),
      (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) *
        coprimeHarmonicMoebius q (N / q) ^ 2 with hTl
  set K := 2 * Z * Real.sqrt N * (2 + Z + Real.log N) + 3 * Z2 with hK
  have hAb : |A| ≤ (J : ℝ) ^ 3 * K := by
    calc |A| ≤ ∑ j ∈ Icc 1 J, (J : ℝ) ^ 2 * K := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hfib)
      _ = (J : ℝ) ^ 3 * K := by
          simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  have hdec : 12 * sievePrimitiveEnergy N moebiusReal / N -
      ∑ j ∈ Icc 1 J, primitiveFibreWeight j / ((j : ℝ) * (j + 1)) = (A + Tl) / N := by
    rw [hsplit, hA, sum_sub_distrib]
    field_simp
    rw [mul_sum]
    have : ∀ j ∈ Icc 1 J, (N : ℝ) * (primitiveFibreWeight j / ((j : ℝ) * (j + 1))) =
        N * primitiveFibreWeight j / ((j : ℝ) * (j + 1)) := fun j _ => by ring
    rw [sum_congr rfl this]
    ring
  rw [hdec, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
  -- `√N ≥ J⁸`
  have hJ8 : (J : ℝ) ^ 8 ≤ Real.sqrt N := by
    have h16 : ((J : ℝ) ^ 8) ^ 2 ≤ N := by
      rw [← pow_mul]; exact_mod_cast hJ16
    exact (le_abs_self _).trans (Real.abs_le_sqrt h16)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hJ7 : (J : ℝ) ^ 7 ≤ N := by
    have : (J : ℝ) ^ 7 ≤ (J : ℝ) ^ 16 := pow_le_pow_right₀ hJR (by norm_num)
    exact this.trans (by exact_mod_cast hJ16)
  have hJ4 : 0 < (J : ℝ) ^ 4 := pow_pos hJ0 4
  -- `J³ K ≤ C N / J⁴`
  have hK1 : (J : ℝ) ^ 3 * K ≤
      (2 * Z * (18 + Z) + 3 * Z2) / (J : ℝ) ^ 4 * N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hJ4]
    have hfac : 2 + Z + Real.log N ≤ (18 + Z) * J := by
      have := le_mul_of_one_le_right hZ0 hJR
      rw [add_mul]; linarith
    have hfac0 : 0 ≤ 2 + Z + Real.log N := by linarith
    have hJ7' : (J : ℝ) ^ 7 * Real.sqrt N * (2 + Z + Real.log N) ≤ (18 + Z) * N := by
      calc (J : ℝ) ^ 7 * Real.sqrt N * (2 + Z + Real.log N)
          ≤ (J : ℝ) ^ 7 * Real.sqrt N * ((18 + Z) * J) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = (18 + Z) * ((J : ℝ) ^ 8 * Real.sqrt N) := by ring
        _ ≤ (18 + Z) * (Real.sqrt N * Real.sqrt N) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJ8 hsqN.le) (by linarith)
        _ = (18 + Z) * N := by rw [hss]
    have e : (J : ℝ) ^ 3 * K * (J : ℝ) ^ 4 =
        2 * Z * ((J : ℝ) ^ 7 * Real.sqrt N * (2 + Z + Real.log N)) + 3 * Z2 * (J : ℝ) ^ 7 := by
      rw [hK]; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hJ7' (by linarith : (0 : ℝ) ≤ 2 * Z)
    have h2 := mul_le_mul_of_nonneg_left hJ7 (by linarith : (0 : ℝ) ≤ 3 * Z2)
    nlinarith
  -- `e^{19/2} ⌊N/(J+1)⌋ ≤ e^{19/2} N/(J+1)`
  have hT1 : Real.exp (19 / 2) * ((N / (J + 1) : ℕ) : ℝ) ≤
      Real.exp (19 / 2) / ((J : ℝ) + 1) * N := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := Nat.cast_div_le (m := N) (n := J + 1) (α := ℝ)
    push_cast at this
    exact this
  calc |A + Tl| ≤ |A| + Tl := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg htail0]
    _ ≤ (J : ℝ) ^ 3 * K + Real.exp (19 / 2) * ((N / (J + 1) : ℕ) : ℝ) := add_le_add hAb htail
    _ ≤ (2 * Z * (18 + Z) + 3 * Z2) / (J : ℝ) ^ 4 * N +
          Real.exp (19 / 2) / ((J : ℝ) + 1) * N := add_le_add hK1 hT1
    _ = _ := by ring

/-- The bound at cutoff `J` tends to zero. -/
theorem tendsto_primitive_bound :
    Tendsto (fun J : ℕ =>
      (2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * (18 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) +
          3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) / (J : ℝ) ^ 4 +
        Real.exp (19 / 2) / ((J : ℝ) + 1) +
        |∑ j ∈ Icc 1 J, primitiveFibreWeight j / ((j : ℝ) * (j + 1)) - moebiusPrimitiveSlope|)
      atTop (𝓝 0) := by
  generalize 2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * (18 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) +
    3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ = C
  have h1 : Tendsto (fun J : ℕ => C / (J : ℝ) ^ 4) atTop (𝓝 0) := by
    have h4 := (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h4).const_mul C
  have h2 : Tendsto (fun J : ℕ => Real.exp (19 / 2) / ((J : ℝ) + 1)) atTop (𝓝 0) := by
    have hl : Tendsto (fun J : ℕ => (J : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hl).const_mul (Real.exp (19 / 2))
  have h3 : Tendsto (fun J : ℕ =>
      |∑ j ∈ Icc 1 J, primitiveFibreWeight j / ((j : ℝ) * (j + 1)) - moebiusPrimitiveSlope|)
      atTop (𝓝 0) := by
    have := (tendsto_sum_primitiveFibreWeight_div.sub_const moebiusPrimitiveSlope).abs
    rwa [sub_self, abs_zero] at this
  have := (h1.add h2).add h3
  rwa [add_zero, add_zero] at this

/-- The fibre cutoff `J = ⌊N^{1/16}⌋` satisfies the hypotheses of the cutoff bound for `N ≥ 2`. -/
theorem fibreCutoff_facts {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ fibreCutoff N ∧ fibreCutoff N < N ∧ Real.log N ≤ 16 * fibreCutoff N := by
  have hJ16 := fibreCutoff_pow_le N
  have hNJ := lt_fibreCutoff_succ_pow N
  generalize fibreCutoff N = J at hJ16 hNJ ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNJR : (N : ℝ) ≤ ((J : ℝ) + 1) ^ 16 := by exact_mod_cast hNJ.le
  have hJ1 : 1 ≤ J := by
    by_contra h
    have hJ0 : J = 0 := by omega
    rw [hJ0] at hNJ
    omega
  clear hNJ
  refine ⟨hJ1, ?_, ?_⟩
  · by_contra h
    have hNle : N ≤ J := by omega
    have h1 : N ^ 16 ≤ J ^ 16 := Nat.pow_le_pow_left hNle 16
    have h2 : N ^ 2 ≤ N ^ 16 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h3 : N ^ 2 ≤ N := h2.trans (h1.trans hJ16)
    have h4 : 2 * N ≤ N ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right N hN
    omega
  · have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    calc Real.log N ≤ Real.log (((J : ℝ) + 1) ^ 16) := Real.log_le_log hN0 hNJR
      _ = 16 * Real.log ((J : ℝ) + 1) := by rw [Real.log_pow]; norm_num
      _ ≤ 16 * J := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < J + 1 by linarith)
          linarith

/-- **The Möbius primitive energy grows linearly.** `12 E_prim(N; μ)/N → c`, with
`c = Σ_{j ≥ 1} T(j)/(j(j+1))`. -/
theorem tendsto_twelve_mul_sievePrimitiveEnergy_moebius_div :
    Tendsto (fun N : ℕ => 12 * sievePrimitiveEnergy N moebiusReal / N) atTop
      (𝓝 moebiusPrimitiveSlope) := by
  have hd : Tendsto (fun N : ℕ => 12 * sievePrimitiveEnergy N moebiusReal / N -
      moebiusPrimitiveSlope) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_primitive_bound.comp tendsto_fibreCutoff)
    filter_upwards [eventually_ge_atTop 2] with N hN
    obtain ⟨hJ1, hJN, hlog⟩ := fibreCutoff_facts hN
    have hpart := abs_twelve_mul_div_sub_partial_le hJ1 hJN (fibreCutoff_pow_le N) hlog
    rw [Real.norm_eq_abs, Function.comp_apply]
    exact (abs_sub_le _ _ _).trans (by linarith)
  have h := hd.add_const moebiusPrimitiveSlope
  rw [zero_add] at h
  exact h.congr fun N => by ring

end

end GaloisForLFunctions.BezoutValuationIncidence

#print axioms GaloisForLFunctions.BezoutValuationIncidence.tendsto_twelve_mul_sievePrimitiveEnergy_moebius_div
#print axioms GaloisForLFunctions.BezoutValuationIncidence.abs_jordanFibreMass_sub_le
