import GaloisForLFunctions.TransHorizonIncidenceMechanics.DivisorIncidencePerturbationAndLogarithmicDamping

/-!
# Weighted coefficient neighborhoods and radical defect stability

Classical baselines: weighted finite ℓ¹ geometry and finite quadratic-form
perturbation. Divisor responses are even arithmetic functions in the sense
of [TH10] https://arxiv.org/abs/1009.5281; the correlation setting is
[CMS16] https://arxiv.org/abs/1612.03136. Classification: New formulation
with known constituents identified; no external priority claim.

Equivalent classical formulation: let
W(N,K;c,b)=Σ_{d≤N}|c(d)−b(d)| floor(K/d). If |s_b|≤B on [1,M+1]
and M+1≤K, then |D_c(M)−D_b(M)|≤4(B+W)W. Only the reference path
needs an amplitude bound. This distance is a seminorm distance on infinite
coefficient functions; coefficients beyond the visible prefix are ignored.

At N≥2,K=6(N+1), the strict Möbius certificate gives
D_c(M)≤−1+4(2+W(N,K;c,μ))W(N,K;c,μ) on every nonempty prefix with
R_N(M+1)<K, provided c has squarefree support. Thus the closed incidence
ball W≤1/20 has margin D_c≤−59/100, uniformly on infinite radical fibers
and positive powers. The more general quadratic budget 4(2+W)W≤1/2
also gives a half-unit margin.

Projecting any direction h onto squarefree coefficients and dividing it by
20(1+W(N,K;h_sf,0)) gives an explicit perturbation of μ strictly inside
the ball, without an assumed smallness input. At prime-family horizons
N=6p−1,p>5, response≥39/20 and defect≤−59/100 coexist at every positive
power of 30p throughout the coefficient ball. First-failure persistence is
not asserted for general perturbations. No optimal-radius or all-damping
claim is made; the unit coefficient is charged by its full incidence count.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false


/-- [Known] Finite weighted coefficient distance charges each divisor by its incidence count. -/
def divisorIncidenceDistance (N K : ℕ) (c b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 N, |c d - b d| * ((K / d : ℕ) : ℝ)

/-- [Known] Divisor-incidence distance is nonnegative. -/
theorem divisorIncidenceDistance_nonneg (N K : ℕ) (c b : ℕ → ℝ) :
    0 ≤ divisorIncidenceDistance N K c b :=
  sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- [Known] Reversing the coefficient pair preserves its incidence distance. -/
theorem divisorIncidenceDistance_symm (N K : ℕ) (c b : ℕ → ℝ) :
    divisorIncidenceDistance N K c b = divisorIncidenceDistance N K b c := by
  unfold divisorIncidenceDistance
  simp only [abs_sub_comm]

/-- [Known] Divisor-incidence distance obeys the triangle inequality. -/
theorem divisorIncidenceDistance_triangle (N K : ℕ) (c b a : ℕ → ℝ) :
    divisorIncidenceDistance N K c a ≤
      divisorIncidenceDistance N K c b + divisorIncidenceDistance N K b a := by
  unfold divisorIncidenceDistance
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro d _
  have h := mul_le_mul_of_nonneg_right (abs_sub_le (c d) (b d) (a d))
    (Nat.cast_nonneg (K / d) : (0 : ℝ) ≤ ((K / d : ℕ) : ℝ))
  nlinarith

/-- [Known] Affine coefficient perturbations have exactly homogeneous incidence distance. -/
theorem divisorIncidenceDistance_add_mul (N K : ℕ) (b h : ℕ → ℝ) (t : ℝ) :
    divisorIncidenceDistance N K (fun d => b d + t * h d) b =
      |t| * divisorIncidenceDistance N K h (fun _ => 0) := by
  unfold divisorIncidenceDistance
  rw [mul_sum]
  apply sum_congr rfl
  intro d _
  simp only [add_sub_cancel_left, sub_zero, abs_mul]
  ring

/-- [Corollary] Every observed response error is controlled by the total incidence budget. -/
theorem abs_sieveSeq_sub_le_divisorIncidenceDistance {N K k : ℕ}
    (hk : 1 ≤ k) (hkK : k ≤ K) (c b : ℕ → ℝ) :
    |sieveSeq N c k - sieveSeq N b k| ≤ divisorIncidenceDistance N K c b :=
  (single_le_sum (fun j _ => abs_nonneg (sieveSeq N c j - sieveSeq N b j))
    (mem_Icc.mpr ⟨hk, hkK⟩)).trans
      (sum_abs_sieveSeq_sub_le_divisor_incidence N K c b)

/-- [New formulation] A bounded reference alone controls defect perturbation through incidence distance. -/
theorem abs_prefix_defect_sub_le_reference_incidence {N M K : ℕ}
    (hMK : M + 1 ≤ K) (c b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ Icc 1 (M + 1), |sieveSeq N b j| ≤ B) :
    |sieveRenormalizedPrefixDefect N M c - sieveRenormalizedPrefixDefect N M b| ≤
      4 * (B + divisorIncidenceDistance N K c b) * divisorIncidenceDistance N K c b := by
  let W := divisorIncidenceDistance N K c b
  have hW : 0 ≤ W := divisorIncidenceDistance_nonneg N K c b
  have hc (j : ℕ) (hj : j ∈ Icc 1 (M + 1)) : |sieveSeq N c j| ≤ B + W := by
    have he := abs_sieveSeq_sub_le_divisorIncidenceDistance (N := N) (mem_Icc.mp hj).1
      ((mem_Icc.mp hj).2.trans hMK) c b
    have ht := abs_add_le (sieveSeq N c j - sieveSeq N b j) (sieveSeq N b j)
    rw [sub_add_cancel] at ht
    have hb' := hb j hj
    dsimp [W]
    linarith
  have he := abs_prefix_defect_sub_le_sum_response_errors N M c b
    (B := B + W) (by linarith) hc (fun j hj => (hb j hj).trans (by linarith))
  have hs : (∑ j ∈ Icc 1 (M + 1), |sieveSeq N c j - sieveSeq N b j|) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hMK)
      (fun j _ _ => abs_nonneg (sieveSeq N c j - sieveSeq N b j))).trans
      (sum_abs_sieveSeq_sub_le_divisor_incidence N K c b)
  exact he.trans (mul_le_mul_of_nonneg_left hs (by positivity))

/-- [New formulation] Every coefficient perturbation has a quantitative finite Möbius-defect margin. -/
theorem prefix_defect_le_moebius_incidence_margin {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hhi : M + 1 < 6 * (N + 1)) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N M c ≤ -1 +
      4 * (2 + divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal) *
        divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal := by
  have hb (j : ℕ) (hj : j ∈ Icc 1 (M + 1)) : |sieveSeq N moebiusReal j| ≤ 2 := by
    have h := abs_sieveSeq_pmPowerDamped_le_two_on_prefix (ε := 0) (le_refl 0)
      (by omega : 1 ≤ N) (mem_Icc.mp hj).1 ((mem_Icc.mp hj).2.trans_lt hhi)
    have hzero : pmPowerDampedRealWeight 0 = moebiusReal := by
      funext d
      simp [pmPowerDampedRealWeight]
    simpa only [hzero] using h
  have he := abs_prefix_defect_sub_le_reference_incidence hhi.le c moebiusReal
    (B := 2) (by norm_num) hb
  have h0 := moebius_prefix_defect_le_neg_one_of_lt_six_succ hN hM hhi
  have hd := (abs_le.mp he).2
  linarith

/-- [New formulation] A finite coefficient neighborhood certifies infinitely many radical endpoints. -/
theorem radical_defect_le_moebius_incidence_margin {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) {c : ℕ → ℝ}
    (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M c ≤ -1 +
      4 * (2 + divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal) *
        divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal :=
  prefix_defect_le_of_finite_radical_certificate hN hM hsf
    (fun k hk hkN => prefix_defect_le_moebius_incidence_margin hN (by omega) (by omega) c) hrN

/-- [Corollary] The full quadratic incidence budget preserves a half-unit negative defect. -/
theorem radical_defect_le_neg_half_of_incidence_budget {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) {c : ℕ → ℝ}
    (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1))
    (hW : 4 * (2 + divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal) *
      divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal ≤ (1 / 2 : ℝ)) :
    sieveRenormalizedPrefixDefect N M c ≤ -(1 / 2 : ℝ) := by
  have h := radical_defect_le_moebius_incidence_margin hN hM hsf hrN
  linarith

/-- [Corollary] The closed incidence ball of radius one twentieth has margin fifty-nine hundredths. -/
theorem radical_defect_le_neg_59_100_of_incidence_distance {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) {c : ℕ → ℝ}
    (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1))
    (hW : divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal ≤ (1 / 20 : ℝ)) :
    sieveRenormalizedPrefixDefect N M c ≤ -(59 / 100 : ℝ) := by
  have h := radical_defect_le_moebius_incidence_margin hN hM hsf hrN
  have h0 := divisorIncidenceDistance_nonneg N (6 * (N + 1)) c moebiusReal
  have hp := mul_nonneg (sub_nonneg.mpr hW) h0
  nlinarith

/-- [Corollary] Every positive power of a certified base inherits the coefficient-neighborhood margin. -/
theorem power_defect_le_neg_59_100_of_incidence_distance {N k m : ℕ}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k < 6 * (N + 1)) (hm : 1 ≤ m)
    {c : ℕ → ℝ} (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hW : divisorIncidenceDistance N (6 * (N + 1)) c moebiusReal ≤ (1 / 20 : ℝ)) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) c ≤ -(59 / 100 : ℝ) := by
  have hd := sieveRenormalizedPrefixDefect_pow_antitone N hsf hk (le_refl 1) hm
  simp only [pow_one] at hd
  have h := prefix_defect_le_moebius_incidence_margin hN (by omega : 1 ≤ k - 1)
    (by omega) c
  have h0 := divisorIncidenceDistance_nonneg N (6 * (N + 1)) c moebiusReal
  have hp := mul_nonneg (sub_nonneg.mpr hW) h0
  nlinarith

/-- [Corollary] Envelope failure and strict negative defect coexist throughout the coefficient neighborhood. -/
theorem incidence_neighborhood_counterfamily_power_separation {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) {c : ℕ → ℝ}
    (hsf : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hW : divisorIncidenceDistance (6 * p - 1) (6 * (6 * p - 1 + 1)) c moebiusReal ≤
      (1 / 20 : ℝ)) {m : ℕ} (hm : 1 ≤ m) :
    (39 / 20 : ℝ) ≤ sieveSeq (6 * p - 1) c ((30 * p) ^ m) ∧
      sieveRenormalizedPrefixDefect (6 * p - 1) ((30 * p) ^ m - 1) c ≤ -(59 / 100 : ℝ) := by
  constructor
  · rw [sieveSeq_pow_of_squarefree_support _ hsf _ hm]
    have he := (abs_sieveSeq_sub_le_divisorIncidenceDistance (N := 6 * p - 1)
      (by omega : 1 ≤ 30 * p) (by omega : 30 * p ≤ 6 * (6 * p - 1 + 1)) c moebiusReal).trans hW
    rw [sieveSeq_moebiusReal_five_horizon_counterfamily hp h5] at he
    have hlo := (abs_le.mp he).1
    linarith
  · exact power_defect_le_neg_59_100_of_incidence_distance (by omega) (by omega)
      (by omega) hm hsf hW

/-- [Known] Squarefree projection restricts an arbitrary perturbation to squarefree coefficient indices. -/
def squarefreePerturbationPart (h : ℕ → ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then h d else 0

/-- [Corollary] Squarefree projection has squarefree support. -/
theorem squarefreePerturbationPart_support (h : ℕ → ℝ) (d : ℕ) (hd : ¬ Squarefree d) :
    squarefreePerturbationPart h d = 0 := by
  simp [squarefreePerturbationPart, hd]

/-- [New formulation] Normalizing any squarefree perturbation gives an explicit Möbius neighborhood weight. -/
def normalizedSquarefreeMobiusPerturbation (N : ℕ) (h : ℕ → ℝ) (d : ℕ) : ℝ :=
  moebiusReal d + (1 / (20 * (1 + divisorIncidenceDistance N (6 * (N + 1))
    (squarefreePerturbationPart h) (fun _ => 0)))) * squarefreePerturbationPart h d

/-- [Corollary] Every normalized perturbation automatically has squarefree support. -/
theorem normalizedSquarefreeMobiusPerturbation_support (N : ℕ) (h : ℕ → ℝ)
    (d : ℕ) (hd : ¬ Squarefree d) : normalizedSquarefreeMobiusPerturbation N h d = 0 := by
  simp [normalizedSquarefreeMobiusPerturbation, squarefreePerturbationPart_support h d hd,
    moebiusReal_eq_zero_of_not_squarefree d hd]

/-- [New formulation] Normalization strictly satisfies the coefficient budget for every perturbation direction. -/
theorem normalizedSquarefreeMobiusPerturbation_distance_lt (N : ℕ) (h : ℕ → ℝ) :
    divisorIncidenceDistance N (6 * (N + 1))
      (normalizedSquarefreeMobiusPerturbation N h) moebiusReal < (1 / 20 : ℝ) := by
  let W := divisorIncidenceDistance N (6 * (N + 1)) (squarefreePerturbationPart h) (fun _ => 0)
  have hW : 0 ≤ W := divisorIncidenceDistance_nonneg _ _ _ _
  have hp : 0 < 20 * (1 + W) := by positivity
  change divisorIncidenceDistance N (6 * (N + 1))
    (fun d => moebiusReal d + (1 / (20 * (1 + W))) * squarefreePerturbationPart h d)
      moebiusReal < _
  rw [divisorIncidenceDistance_add_mul, abs_of_pos (by positivity : 0 < 1 / (20 * (1 + W)))]
  change 1 / (20 * (1 + W)) * W < _
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_lt_iff₀ hp).mpr
  linarith

/-- [New formulation] Every normalized direction has strict negative defect on every certified radical fiber. -/
theorem normalizedSquarefreeMobiusPerturbation_radical_defect_lt {N M : ℕ}
    (hN : 2 ≤ N) (hM : 1 ≤ M)
    (hrN : horizonRadicalState N (M + 1) < 6 * (N + 1)) (h : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N M (normalizedSquarefreeMobiusPerturbation N h) <
      -(59 / 100 : ℝ) := by
  have hb := radical_defect_le_moebius_incidence_margin hN hM
    (normalizedSquarefreeMobiusPerturbation_support N h) hrN
  have hW := normalizedSquarefreeMobiusPerturbation_distance_lt N h
  have h0 := divisorIncidenceDistance_nonneg N (6 * (N + 1))
    (normalizedSquarefreeMobiusPerturbation N h) moebiusReal
  have hp := mul_nonneg (sub_nonneg.mpr hW.le) h0
  nlinarith

/-- [Corollary] Every normalized direction preserves a strict negative margin along all positive powers. -/
theorem normalizedSquarefreeMobiusPerturbation_power_defect_lt {N k m : ℕ}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k < 6 * (N + 1)) (hm : 1 ≤ m) (h : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N (k ^ m - 1) (normalizedSquarefreeMobiusPerturbation N h) <
      -(59 / 100 : ℝ) := by
  have hd := sieveRenormalizedPrefixDefect_pow_antitone N
    (normalizedSquarefreeMobiusPerturbation_support N h) hk (le_refl 1) hm
  simp only [pow_one] at hd
  have hb := prefix_defect_le_moebius_incidence_margin hN (by omega : 1 ≤ k - 1)
    (by omega) (normalizedSquarefreeMobiusPerturbation N h)
  have hW := normalizedSquarefreeMobiusPerturbation_distance_lt N h
  have h0 := divisorIncidenceDistance_nonneg N (6 * (N + 1))
    (normalizedSquarefreeMobiusPerturbation N h) moebiusReal
  have hp := mul_nonneg (sub_nonneg.mpr hW.le) h0
  nlinarith

/-- [New formulation] Every normalized direction gives an explicit power family with envelope failure and negative defect. -/
theorem normalizedSquarefreeMobiusPerturbation_counterfamily {p : ℕ}
    (hp : p.Prime) (h5 : 5 < p) (h : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (39 / 20 : ℝ) < sieveSeq (6 * p - 1)
      (normalizedSquarefreeMobiusPerturbation (6 * p - 1) h) ((30 * p) ^ m) ∧
      sieveRenormalizedPrefixDefect (6 * p - 1) ((30 * p) ^ m - 1)
        (normalizedSquarefreeMobiusPerturbation (6 * p - 1) h) < -(59 / 100 : ℝ) := by
  constructor
  · rw [sieveSeq_pow_of_squarefree_support _ (normalizedSquarefreeMobiusPerturbation_support _ h) _ hm]
    have he := (abs_sieveSeq_sub_le_divisorIncidenceDistance (N := 6 * p - 1)
      (by omega : 1 ≤ 30 * p) (by omega : 30 * p ≤ 6 * (6 * p - 1 + 1))
      (normalizedSquarefreeMobiusPerturbation (6 * p - 1) h) moebiusReal).trans_lt
        (normalizedSquarefreeMobiusPerturbation_distance_lt _ h)
    rw [sieveSeq_moebiusReal_five_horizon_counterfamily hp h5] at he
    have hlo := (abs_lt.mp he).1
    linarith
  · exact normalizedSquarefreeMobiusPerturbation_power_defect_lt (by omega) (by omega)
      (by omega) hm h

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
