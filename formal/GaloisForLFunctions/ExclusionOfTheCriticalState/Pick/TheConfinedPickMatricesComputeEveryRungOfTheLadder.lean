import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.WindowTestsCarryTheNegativeSpacesOfTheConfinedForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesCountTheZerosRightOfTheLine

/-!
# The confined Pick matrices compute every rung of the critical ladder

Let `Φ_0, …, Φ_k` be a critical ladder with ratios `R_0 ≤ … ≤ R_k` and let `Pick_N(r)` be the real
Pick matrix `(Q_r(e_m, e_n))_{7 ≤ m, n ≤ N + 6}` of the confined form on the integer probes.

* **At most `j` negative squares up to `R_j`** (`IsCriticalLadder.hermNegIndex_confinedProbeGram_le`).
  For `r ≤ R_j` a probe sum `X` that is `W₈`-orthogonal to `Φ_0, …, Φ_{j-1}` splits as
  `X = Z + Σ_i α_i Φ_i` with `Z` orthogonal to every rung; the null vectors pair through `W₈` only, so
  `Q_r(X) = Q_r(Z) + Σ_{i ≥ j} α_i² (a(r) - a(R_i)) W₈(Φ_i) ≥ 0` by the floor of the ladder. A
  negative subspace of dimension `> j` would contain such an `X`.
* **At least `j + 1` beyond `R_j`** (`IsCriticalLadder.exists_le_hermNegIndex`). For `r > R_j`,
  `Q_r ≤ -(a(R_j) - a(r))|t|²` on the span of `Φ_0, …, Φ_j`; window tests carry this negative space
  (`exists_window_family_of_negative`), and probe sums approximate a family of window tests uniformly
  (`exists_pick_family_of_window`: one polynomial approximation per test, zero coordinates in `ℓ²` and
  `|G - P| ≤ εe^{6u}`, linear in the family).
* **Every rung in Pick form** (`IsCriticalLadder.isGreatest_confinedPick`). `R_j` is the largest
  ratio at which no integer Pick matrix has more than `j` negative squares; in particular the
  ratios of a ladder do not depend on the ladder (`IsCriticalLadder.ratio_eq`).
-/

open MeasureTheory Set Filter Topology Complex Matrix
open scoped ComplexConjugate lp

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry Zeta23
  _root_.RHTower HeckeKreinToeplitz CohomologyOfWindowsOfSpecZ

local notation "W8" => criticalHalfLineExponentialPair
local notation "Q" => criticalHalfLineFullEnergy

theorem pickNodes_one_le (N : ℕ) : ∀ k : Fin N, 1 ≤ (k : ℝ) + 7 := fun k => by
  linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]

theorem pickNodes_four_lt (N : ℕ) : ∀ k : Fin N, 4 < (k : ℝ) + 7 := fun k => by
  linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]

/-- The constant `2√(5 Σ_ρ m_ρ/(1 + |ρ - ½|²))` bounding zero coordinates. -/
def zeroCoordConstant : ℝ :=
  2 * Real.sqrt (5 * ∑' τ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2)))

theorem zeroCoordConstant_nonneg : 0 ≤ zeroCoordConstant := by
  unfold zeroCoordConstant; positivity

/-! ### Linear algebra of probe sums -/

theorem probeSum_finsetSum_coeff {N m : ℕ} (p : Fin N → ℝ) (t : Fin m → ℝ)
    (c : Fin m → Fin N → ℝ) (u : ℝ) :
    probeSum p (fun k => ∑ i, t i * c i k) u = ∑ i, t i * probeSum p (c i) u := by
  simp only [probeSum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem windowProfile_finsetSum {m : ℕ} (H : Fin m → ℝ → ℝ) (t : Fin m → ℝ) (x : ℝ) :
    windowProfile (fun u => ∑ i, t i * H i u) x = ∑ i, t i * windowProfile (H i) x := by
  unfold windowProfile
  split_ifs
  · rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

theorem confinedPickForm_smul (R s : ℝ) {N : ℕ} (v : Fin N → ℝ) :
    confinedPickForm R (fun k => s * v k) = s ^ 2 * confinedPickForm R v := by
  unfold confinedPickForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem probeSumVec_zero {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k) :
    probeSumVec hp (fun _ => 0) = 0 := by
  unfold probeSumVec
  exact Finset.sum_eq_zero fun k _ => by rw [Complex.ofReal_zero, zero_smul]

theorem probeSum_antiderivPoly_pad (π : Polynomial ℝ) {N : ℕ} (hN : π.natDegree + 1 ≤ N) :
    probeSum (fun k : Fin N => (k : ℝ) + 7) (fun k => π.coeff k / ((k : ℝ) + 1)) =
      probeSum (fun k : Fin (π.natDegree + 1) => (k : ℝ) + 7)
        (fun k => π.coeff k / ((k : ℝ) + 1)) := by
  funext u
  have h1 := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => π.coeff k / ((k : ℝ) + 1) * probe ((k : ℝ) + 7) u) N
  have h2 := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => π.coeff k / ((k : ℝ) + 1) * probe ((k : ℝ) + 7) u) (π.natDegree + 1)
  simp only [probeSum]
  rw [h1, h2]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun k _ hk => ?_
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range] at hk; omega),
    zero_div, zero_mul]

/-- On real vectors the Hermitian form of the confined Pick matrix is its Pick form. -/
theorem hermQuad_confinedProbeGram_ofReal (r : ℝ) {N : ℕ} (v : Fin N → ℝ) :
    hermQuad (confinedProbeGram r (fun k : Fin N => (k : ℝ) + 7)) (fun n => (v n : ℂ)) =
      confinedPickForm r v := by
  rw [show confinedProbeGram r (fun k : Fin N => (k : ℝ) + 7) = fun (a b : Fin N) =>
      ((criticalHalfLineMixedEnergy r (probe ((a : ℝ) + 7)) (probe ((b : ℝ) + 7)) : ℝ) : ℂ) from rfl,
    hermQuad_ofReal_eq]
  unfold confinedPickForm
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ### One window test against one probe sum -/

/-- **A nearby probe sum has nearly the energy of a window test.** If the zero coordinates differ
by at most `εB` and `|G - P| ≤ εe^{6u}`, the Pick form of `P` exceeds `Q_R(G)` by at most
`εB(2‖y_G‖ + εB) + a(R)(2ε∫|G|e^{-2u} + ε²)`. -/
theorem confinedPickForm_le_of_near {R : ℝ} (hR : 0 < R) {A : ℝ} {G : ℝ → ℝ}
    (hG : IsWindowTest A G) {N : ℕ} (c : Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hy : ‖windowVec hG - probeSumVec (pickNodes_one_le N) c‖ ≤ ε * zeroCoordConstant)
    (hD : ∀ u, u < 0 →
      |G u - probeSum (fun k : Fin N => (k : ℝ) + 7) c u| ≤ ε * Real.exp (6 * u)) :
    confinedPickForm R c ≤ Q R G +
      ε * zeroCoordConstant * (2 * ‖windowVec hG‖ + ε * zeroCoordConstant) +
      criticalAliasCoefficient R * (2 * ε * (∫ u, |G u| * Real.exp (-(2 * u))) + ε ^ 2) := by
  have ha : 0 ≤ criticalAliasCoefficient R := (criticalAliasCoefficient_positive hR).le
  have hB := zeroCoordConstant_nonneg
  set y := windowVec hG
  have hQ : Q R G = (inner ℂ (reflectVec zetaZeroConfig y) y).re +
      criticalAliasCoefficient R * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
    rw [fullEnergy_eq_weilQuad_add hG.contDiff hG.hasCompactSupport
      (windowTest_vanish_nonneg hG), weilQuad_eq_re_inner_windowVec hG]
  have hK := re_inner_reflect_le y (probeSumVec (pickNodes_one_le N) c)
  have hW := integral_probeSum_sq_le hG (pickNodes_four_lt N) c hε hD
  rw [← sum_div_eq_integral_probeSum_sq (pickNodes_four_lt N) c] at hW
  have hd : ‖probeSumVec (pickNodes_one_le N) c - y‖ ≤ ε * zeroCoordConstant := by
    rw [norm_sub_rev]; exact hy
  have e1 : ‖probeSumVec (pickNodes_one_le N) c - y‖ *
      (2 * ‖y‖ + ‖probeSumVec (pickNodes_one_le N) c - y‖) ≤
      ε * zeroCoordConstant * (2 * ‖y‖ + ε * zeroCoordConstant) :=
    mul_le_mul hd (by linarith) (by positivity) (by positivity)
  have e2 := mul_le_mul_of_nonneg_left hW ha
  rw [confinedPickForm_eq R c (pickNodes_one_le N), hQ]
  linarith

/-- The zero coordinates of a window test are bounded by its profile: `|g|, |g'| ≤ L` on `[0, 1]`
gives `‖y_G‖ ≤ L B`. -/
theorem norm_windowVec_le {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) {L : ℝ} (hL0 : 0 ≤ L)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |windowProfile G x| ≤ L)
    (hb' : ∀ x ∈ Icc (0 : ℝ) 1, |deriv (windowProfile G) x| ≤ L) :
    ‖windowVec hG‖ ≤ L * zeroCoordConstant := by
  have hg := contDiff_windowProfile hG
  have h := norm_windowVec_sub_probeSumVec_le hG (pickNodes_one_le 0) (fun _ => 0) hL0 fun τ =>
    norm_integral_error_le (φ := windowProfile G) (φ' := deriv (windowProfile G))
      (fun x => ((hg.differentiable two_ne_zero) x).hasDerivAt) (hg.continuous_deriv one_le_two)
      hL0 hb hb' (fun u _ => by simp [probeSum, windowProfile_exp])
      (fun u hu => by simp [probeSum, windowTest_vanish_nonneg hG u hu])
      (re_carrier_sub_half_ge τ)
  rw [probeSumVec_zero, sub_zero] at h
  refine h.trans (le_of_eq ?_)
  unfold zeroCoordConstant
  ring

/-! ### A family of window tests against probe sums -/

/-- **Probe sums carry a negative space of window tests.** If `Q_R ≤ -η|t|²` on the span of window
tests `H_0, …, H_{m-1}`, some integer node set carries real vectors `c_i` with
`Pick_R(Σ_i t_i c_i) < 0` for every `t ≠ 0`. -/
theorem exists_pick_family_of_window {R : ℝ} (hR : 0 < R) {m : ℕ} {A : ℝ}
    {H : Fin m → ℝ → ℝ} (hH : ∀ i, IsWindowTest A (H i)) {η : ℝ} (hη : 0 < η)
    (hneg : ∀ t : Fin m → ℝ, Q R (fun u => ∑ i, t i * H i u) ≤ -(η * ∑ i, t i ^ 2)) :
    ∃ (N : ℕ) (c : Fin m → Fin N → ℝ), ∀ t : Fin m → ℝ, t ≠ 0 →
      confinedPickForm R (fun k => ∑ i, t i * c i k) < 0 := by
  classical
  have ha : 0 ≤ criticalAliasCoefficient R := (criticalAliasCoefficient_positive hR).le
  have hB := zeroCoordConstant_nonneg
  have hgd : ∀ i, ContDiff ℝ 2 (windowProfile (H i)) := fun i => contDiff_windowProfile (hH i)
  -- uniform bounds for the profiles and their derivatives on [0, 1]
  have hbd : ∀ i, ∃ L, 0 ≤ L ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |windowProfile (H i) x| ≤ L ∧ |deriv (windowProfile (H i)) x| ≤ L := by
    intro i
    obtain ⟨L1, hL1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hgd i).continuous.continuousOn
    obtain ⟨L2, hL2⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hgd i).continuous_deriv one_le_two).continuousOn
    refine ⟨max (max L1 L2) 0, le_max_right _ _, fun x hx => ⟨?_, ?_⟩⟩
    · have h := hL1 x hx
      rw [Real.norm_eq_abs] at h
      exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have h := hL2 x hx
      rw [Real.norm_eq_abs] at h
      exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  choose L hL0 hL using hbd
  have hJi : ∀ i, Integrable fun u => |H i u| * Real.exp (-(2 * u)) := fun i =>
    (show Continuous (fun u => |H i u| * Real.exp (-(2 * u))) by
      have := (hH i).continuous; fun_prop).integrable_of_hasCompactSupport
      ((hH i).hasCompactSupport.mono fun u hu h0 => hu (by simp only [h0, abs_zero, zero_mul]))
  set Ls := ∑ i, L i with hLsdef
  set Js := ∑ i, ∫ u, |H i u| * Real.exp (-(2 * u)) with hJsdef
  have hLs : 0 ≤ Ls := Finset.sum_nonneg fun i _ => hL0 i
  have hJs : 0 ≤ Js := Finset.sum_nonneg fun i _ => integral_nonneg fun u => by positivity
  set K := zeroCoordConstant * (2 * (Ls * zeroCoordConstant) + zeroCoordConstant) +
    criticalAliasCoefficient R * (2 * Js + 1) with hKdef
  have hK : 0 ≤ K := by positivity
  set ε := min 1 (η / (2 * ((m : ℝ) + 1) * (K + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : ε * K ≤ η / (2 * ((m : ℝ) + 1)) := by
    have h := min_le_right 1 (η / (2 * ((m : ℝ) + 1) * (K + 1)))
    have hK1 : K + 1 ≠ 0 := by positivity
    have h2 : ε * (K + 1) ≤ η / (2 * ((m : ℝ) + 1) * (K + 1)) * (K + 1) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have h3 : η / (2 * ((m : ℝ) + 1) * (K + 1)) * (K + 1) = η / (2 * ((m : ℝ) + 1)) := by
      field_simp
    nlinarith
  choose π hπd hπ using fun i => exists_antiderivPoly_near (hH i) hε
  set N := ∑ i, ((π i).natDegree + 1) with hNdef
  have hN : ∀ i, (π i).natDegree + 1 ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => (π i).natDegree + 1) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  set c : Fin m → Fin N → ℝ := fun i k => (π i).coeff k / ((k : ℝ) + 1) with hcdef
  have hP : ∀ i u, u < 0 → Real.exp (6 * u) * antiderivPoly (π i) (Real.exp u) =
      probeSum (fun k : Fin N => (k : ℝ) + 7) (c i) u := fun i u hu => by
    rw [exp_mul_antiderivPoly_eq_probeSum (π i) hu, ← probeSum_antiderivPoly_pad (π i) (hN i)]
  -- the estimate on the unit ball of `ℓ¹`
  have hmain : ∀ t : Fin m → ℝ, (∑ i, |t i|) ≤ 1 →
      confinedPickForm R (fun k => ∑ i, t i * c i k) ≤
        Q R (fun u => ∑ i, t i * H i u) + ε * K := by
    intro t ht
    have hti : ∀ i, |t i| ≤ 1 := fun i => (Finset.single_le_sum (f := fun i => |t i|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)).trans ht
    have hG : IsWindowTest A (fun u => ∑ i, t i * H i u) := isWindowTest_finsetSum Finset.univ hH t
    have hg : ∀ x, windowProfile (fun u => ∑ i, t i * H i u) x =
        ∑ i, t i * windowProfile (H i) x := windowProfile_finsetSum H t
    have hgD : ∀ x, HasDerivAt (windowProfile (fun u => ∑ i, t i * H i u))
        (∑ i, t i * deriv (windowProfile (H i)) x) x := by
      intro x
      rw [show windowProfile (fun u => ∑ i, t i * H i u) =
        fun y => ∑ i, t i * windowProfile (H i) y from funext hg]
      exact HasDerivAt.fun_sum fun i _ =>
        (((hgd i).differentiable two_ne_zero) x).hasDerivAt.const_mul (t i)
    have hφd : ∀ x, HasDerivAt
        (fun x => windowProfile (fun u => ∑ i, t i * H i u) x - ∑ i, t i * antiderivPoly (π i) x)
        ((∑ i, t i * deriv (windowProfile (H i)) x) - ∑ i, t i * (π i).eval x) x := fun x =>
      (hgD x).sub (HasDerivAt.fun_sum fun i _ =>
        (hasDerivAt_antiderivPoly (π i) x).const_mul (t i))
    have hφ'c : Continuous fun x =>
        (∑ i, t i * deriv (windowProfile (H i)) x) - ∑ i, t i * (π i).eval x :=
      (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((hgd i).continuous_deriv one_le_two)).sub
        (continuous_finsetSum _ fun i _ => continuous_const.mul (Polynomial.continuous _))
    have hsum_le : ∀ (f : Fin m → ℝ) (b : ℝ), 0 ≤ b → (∀ i, |f i| ≤ b) →
        |∑ i, t i * f i| ≤ b := fun f b hb hf => by
      calc |∑ i, t i * f i| ≤ ∑ i, |t i * f i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |t i| * b := Finset.sum_le_sum fun i _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
        _ = (∑ i, |t i|) * b := by rw [Finset.sum_mul]
        _ ≤ 1 * b := mul_le_mul_of_nonneg_right ht hb
        _ = b := one_mul b
    have hφb : ∀ x ∈ Icc (0 : ℝ) 1, |windowProfile (fun u => ∑ i, t i * H i u) x -
        ∑ i, t i * antiderivPoly (π i) x| ≤ ε := fun x hx => by
      rw [hg, ← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      exact hsum_le _ ε hε.le fun i => hπ i x hx
    have hφ'b : ∀ x ∈ Icc (0 : ℝ) 1, |(∑ i, t i * deriv (windowProfile (H i)) x) -
        ∑ i, t i * (π i).eval x| ≤ ε := fun x hx => by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      exact hsum_le _ ε hε.le fun i => hπd i x hx
    have hDneg : ∀ u, u < 0 → (∑ i, t i * H i u) -
        probeSum (fun k : Fin N => (k : ℝ) + 7) (fun k => ∑ i, t i * c i k) u =
          Real.exp (6 * u) * (windowProfile (fun u => ∑ i, t i * H i u) (Real.exp u) -
            ∑ i, t i * antiderivPoly (π i) (Real.exp u)) := by
      intro u hu
      rw [probeSum_finsetSum_coeff, mul_sub, windowProfile_exp, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← hP i u hu]; ring
    have hD0 : ∀ u, 0 ≤ u → (∑ i, t i * H i u) -
        probeSum (fun k : Fin N => (k : ℝ) + 7) (fun k => ∑ i, t i * c i k) u = 0 := by
      intro u hu
      rw [windowTest_vanish_nonneg hG u hu]
      simp [probeSum, probe_of_nonneg hu]
    have hyb := norm_windowVec_sub_probeSumVec_le hG (pickNodes_one_le N)
      (fun k => ∑ i, t i * c i k) hε.le fun τ => norm_integral_error_le hφd hφ'c hε.le hφb hφ'b
        hDneg hD0 (re_carrier_sub_half_ge τ)
    have hy : ‖windowVec hG - probeSumVec (pickNodes_one_le N) (fun k => ∑ i, t i * c i k)‖ ≤
        ε * zeroCoordConstant := by
      refine hyb.trans (le_of_eq ?_)
      unfold zeroCoordConstant
      ring
    have hDabs : ∀ u, u < 0 → |(∑ i, t i * H i u) -
        probeSum (fun k : Fin N => (k : ℝ) + 7) (fun k => ∑ i, t i * c i k) u| ≤
          ε * Real.exp (6 * u) := fun u hu => by
      rw [hDneg u hu, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm ε]
      exact mul_le_mul_of_nonneg_left
        (hφb _ ⟨(Real.exp_pos u).le, Real.exp_le_one_iff.mpr hu.le⟩) (Real.exp_pos _).le
    have hnear := confinedPickForm_le_of_near hR hG _ hε.le hy hDabs
    have hyG : ‖windowVec hG‖ ≤ Ls * zeroCoordConstant := by
      refine norm_windowVec_le hG hLs (fun x hx => ?_) (fun x hx => ?_)
      · rw [hg]
        refine (hsum_le _ (Ls) hLs fun i => ?_)
        exact (hL i x hx).1.trans (Finset.single_le_sum (f := L) (fun j _ => hL0 j)
          (Finset.mem_univ i))
      · rw [(hgD x).deriv]
        refine (hsum_le _ (Ls) hLs fun i => ?_)
        exact (hL i x hx).2.trans (Finset.single_le_sum (f := L) (fun j _ => hL0 j)
          (Finset.mem_univ i))
    have hJG : (∫ u, |∑ i, t i * H i u| * Real.exp (-(2 * u))) ≤ Js := by
      have hint : Integrable fun u => ∑ i, |t i| * (|H i u| * Real.exp (-(2 * u))) :=
        integrable_finsetSum _ fun i _ => (hJi i).const_mul _
      calc (∫ u, |∑ i, t i * H i u| * Real.exp (-(2 * u)))
          ≤ ∫ u, ∑ i, |t i| * (|H i u| * Real.exp (-(2 * u))) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) hint
              (Eventually.of_forall fun u => ?_)
            show |∑ i, t i * H i u| * Real.exp (-(2 * u)) ≤
              ∑ i, |t i| * (|H i u| * Real.exp (-(2 * u)))
            have h1 : |∑ i, t i * H i u| ≤ ∑ i, |t i| * |H i u| :=
              (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq
                (Finset.sum_congr rfl fun i _ => abs_mul _ _))
            have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(2 * u))).le
            rw [Finset.sum_mul] at h2
            exact h2.trans (le_of_eq (Finset.sum_congr rfl fun i _ => by ring))
        _ = ∑ i, |t i| * ∫ u, |H i u| * Real.exp (-(2 * u)) := by
            rw [integral_finsetSum _ fun i _ => (hJi i).const_mul _]
            exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
        _ ≤ Js := Finset.sum_le_sum fun i _ => by
            have h0 : 0 ≤ ∫ u, |H i u| * Real.exp (-(2 * u)) :=
              integral_nonneg fun u => by positivity
            nlinarith [hti i, abs_nonneg (t i)]
    have hεB : ε * zeroCoordConstant ≤ zeroCoordConstant := by nlinarith
    have t1 : ε * zeroCoordConstant * (2 * ‖windowVec hG‖ + ε * zeroCoordConstant) ≤
        ε * zeroCoordConstant * (2 * (Ls * zeroCoordConstant) + zeroCoordConstant) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have t2 : criticalAliasCoefficient R *
        (2 * ε * (∫ u, |∑ i, t i * H i u| * Real.exp (-(2 * u))) + ε ^ 2) ≤
        criticalAliasCoefficient R * (2 * ε * Js + ε) := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      have h1 := mul_le_mul_of_nonneg_left hJG (by positivity : (0 : ℝ) ≤ 2 * ε)
      nlinarith
    have eK : ε * K = ε * zeroCoordConstant * (2 * (Ls * zeroCoordConstant) + zeroCoordConstant) +
        criticalAliasCoefficient R * (2 * ε * Js + ε) := by
      rw [hKdef]; ring
    linarith
  refine ⟨N, c, fun t ht => ?_⟩
  set s := ∑ i, |t i| with hsdef
  have hs : 0 < s := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    exact lt_of_lt_of_le (abs_pos.mpr hi) (Finset.single_le_sum (f := fun i => |t i|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hs0 : s ≠ 0 := hs.ne'
  set t' : Fin m → ℝ := fun i => t i / s with ht'def
  have ht'1 : ∑ i, |t' i| = 1 := by
    simp only [ht'def, abs_div, abs_of_pos hs, ← Finset.sum_div]
    exact div_self hs0
  have hm1 := hmain t' ht'1.le
  have hq := hneg t'
  have hcs : (1 : ℝ) ≤ (m : ℝ) * ∑ i, t' i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => |t' i|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    rw [ht'1, one_pow] at h
    exact_mod_cast h
  have hsum0 : 0 ≤ ∑ i, t' i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm2 : (1 : ℝ) ≤ ((m : ℝ) + 1) * ∑ i, t' i ^ 2 := by nlinarith
  have hkey : η / (2 * ((m : ℝ) + 1)) < η * ∑ i, t' i ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hneg' : confinedPickForm R (fun k => ∑ i, t' i * c i k) < 0 := by linarith
  have hct : (fun k => ∑ i, t i * c i k) = fun k => s * ∑ i, t' i * c i k := by
    funext k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [ht'def]; field_simp
  rw [hct, confinedPickForm_smul]
  exact mul_neg_of_pos_of_neg (by positivity) hneg'

/-! ### From Pick forms to negative squares -/

/-- **A negative family of real vectors gives negative squares.** -/
theorem le_hermNegIndex_of_confinedPickForm_neg {r : ℝ} {N m : ℕ} (c : Fin m → Fin N → ℝ)
    (hneg : ∀ t : Fin m → ℝ, t ≠ 0 → confinedPickForm r (fun k => ∑ i, t i * c i k) < 0) :
    m ≤ hermNegIndex (confinedProbeGram r (fun k : Fin N => (k : ℝ) + 7)) := by
  classical
  set M := confinedProbeGram r (fun k : Fin N => (k : ℝ) + 7) with hM
  have hreal : ∀ a b, (M a b).im = 0 := fun a b => Complex.ofReal_im _
  have hle : ∀ t : Fin m → ℝ, confinedPickForm r (fun k => ∑ i, t i * c i k) ≤ 0 := fun t => by
    by_cases ht : t = 0
    · subst ht; simp [confinedPickForm]
    · exact (hneg t ht).le
  let T : (Fin m → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun z k => ∑ i, z i * (c i k : ℂ)
      map_add' := fun z w => by
        funext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a z => by
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hTre : ∀ z : Fin m → ℂ, (fun k => ((T z k).re : ℂ)) =
      fun k => (((∑ i, (z i).re * c i k : ℝ)) : ℂ) := fun z => by
    funext k
    simp [T, Complex.re_sum, Complex.mul_re]
  have hTim : ∀ z : Fin m → ℂ, (fun k => ((T z k).im : ℂ)) =
      fun k => (((∑ i, (z i).im * c i k : ℝ)) : ℂ) := fun z => by
    funext k
    simp [T, Complex.im_sum, Complex.mul_im]
  have hT : ∀ z : Fin m → ℂ, z ≠ 0 → hermQuad M (T z) < 0 := by
    intro z hz
    rw [hermQuad_eq_re_add_im hreal, hTre, hTim, hermQuad_confinedProbeGram_ofReal,
      hermQuad_confinedProbeGram_ofReal]
    by_cases hre : (fun i => (z i).re) = 0
    · have him : (fun i => (z i).im) ≠ 0 := by
        intro him
        apply hz
        funext i
        exact Complex.ext (congrFun hre i) (congrFun him i)
      have h1 := hneg _ him
      have h2 := hle (fun i => (z i).re)
      linarith
    · have h1 := hneg _ hre
      have h2 := hle (fun i => (z i).im)
      linarith
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    by_contra hz0
    have h := hT z hz0
    rw [LinearMap.mem_ker.mp hz] at h
    simp [hermQuad] at h
  have hW : IsPosDefOn (-M) (LinearMap.range T) := by
    rintro x ⟨z, rfl⟩ hx
    have hz : z ≠ 0 := fun h => hx (by rw [h, map_zero])
    rw [hermQuad_neg]
    linarith [hT z hz]
  have h := finrank_le_posIndex hW
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun] at h
  exact h

/-! ### The ladder in Pick form -/

theorem criticalHalfLineExponentialPair_zero_right (F : ℝ → ℝ) : W8 F (fun _ => 0) = 0 := by
  simp [criticalHalfLineExponentialPair]

/-- `W₈` against a probe sum is the combination of `W₈` against the probes. -/
theorem exponentialPair_probeSum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {N : ℕ}
    (v : Fin N → ℝ) :
    W8 F (probeSum (fun k : Fin N => (k : ℝ) + 7) v) =
      ∑ n, v n * W8 F (probe ((n : ℝ) + 7)) := by
  have hZ : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) :=
    criticalHalfLineEnergyDomain_of_compact_negative contDiff_const HasCompactSupport.zero
      fun _ _ => rfl
  have h := exponentialPair_add_sum hF hZ
    (fun n => criticalHalfLineEnergyDomain_probe (pickNodes_four_lt N n)) v Finset.univ
  rw [criticalHalfLineExponentialPair_zero_right, zero_add] at h
  rw [← h]
  congr 1
  funext u
  simp [probeSum]

/-- **At most `j` negative squares up to the `j`-th rung.** -/
theorem IsCriticalLadder.hermNegIndex_confinedProbeGram_le {k : ℕ} {R : Fin (k + 1) → ℝ}
    {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ) (j : Fin (k + 1)) {r : ℝ}
    (hr : 0 < r) (hrj : r ≤ R j) (N : ℕ) :
    hermNegIndex (confinedProbeGram r (fun i : Fin N => (i : ℝ) + 7)) ≤ j := by
  classical
  set M := confinedProbeGram r (fun i : Fin N => (i : ℝ) + 7)
  have hD : ∀ i, CriticalHalfLineEnergyDomain (Φ i) := fun i => (hL.null i).1
  have hDp : ∀ n : Fin N, CriticalHalfLineEnergyDomain (probe ((n : ℝ) + 7)) := fun n =>
    criticalHalfLineEnergyDomain_probe (pickNodes_four_lt N n)
  have hw : ∀ i, 0 < W8 (Φ i) (Φ i) := fun i =>
    exponentialPair_self_pos (hD i) (by rw [hL.unit i]; norm_num)
  -- nonnegativity on probe sums orthogonal to the rungs below `j`
  have hpos : ∀ v : Fin N → ℝ, (∀ i : Fin (k + 1), i < j →
      W8 (Φ i) (probeSum (fun k : Fin N => (k : ℝ) + 7) v) = 0) → 0 ≤ confinedPickForm r v := by
    intro v hv
    rw [confinedPickForm_eq_fullEnergy]
    set X := probeSum (fun k : Fin N => (k : ℝ) + 7) v with hXdef
    have hX : CriticalHalfLineEnergyDomain X := criticalHalfLineEnergyDomain_finsetSum _ hDp v
    set α : Fin (k + 1) → ℝ := fun i => W8 (Φ i) X / W8 (Φ i) (Φ i) with hαdef
    set Z : ℝ → ℝ := fun u => X u + ∑ i, (-α i) * Φ i u with hZdef
    have hZ : CriticalHalfLineEnergyDomain Z :=
      criticalHalfLineEnergyDomain_add_sum hX hD (fun i => -α i) Finset.univ
    have hZo : ∀ l, W8 (Φ l) Z = 0 := by
      intro l
      rw [hZdef, exponentialPair_add_sum (hD l) hX hD (fun i => -α i) Finset.univ,
        Finset.sum_eq_single l]
      · simp only [hαdef]
        field_simp [(hw l).ne']
        ring
      · intro i _ hil
        rw [hL.orth l i (Ne.symm hil), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ l) h
    have hXZ : X = fun u => Z u + ∑ i, α i * Φ i u := by
      funext u
      simp only [hZdef, neg_mul, Finset.sum_neg_distrib]
      ring
    have hQ := fullEnergy_add_sum_nullVectors r hL.null hL.orth hZ hZo α Finset.univ
    rw [← hXZ] at hQ
    rw [hQ]
    have hfloor := hL.floor r hr (hrj.trans (hL.mono (Fin.le_last j))) Z hZ hZo
    refine add_nonneg hfloor (Finset.sum_nonneg fun i _ => ?_)
    by_cases hij : i < j
    · have h0 : α i = 0 := by simp only [hαdef, hv i hij, zero_div]
      rw [h0]
      simp
    · have hRi : R j ≤ R i := hL.mono (not_lt.mp hij)
      have ha : criticalAliasCoefficient (R i) ≤ criticalAliasCoefficient r := by
        rw [criticalAliasCoefficient_eq_div (R i), criticalAliasCoefficient_eq_div r]
        exact div_le_div_of_nonneg_left (criticalAliasCoefficient_positive one_pos).le hr
          (hrj.trans hRi)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (hw i).le)
  -- a negative subspace of dimension > j meets the orthogonality constraints
  obtain ⟨W, hWr, hWpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-M)
  by_contra hlt
  push Not at hlt
  have hWj : (j : ℕ) < Module.finrank ℂ W := by
    have h : hermNegIndex M = hermPosIndex (-M) := rfl
    omega
  let L : (Fin N → ℂ) →ₗ[ℂ] (Fin j → ℂ) :=
    { toFun := fun x i => ∑ n, x n *
        (W8 (Φ (Fin.castLE (le_of_lt j.2) i)) (probe ((n : ℝ) + 7)) : ℂ)
      map_add' := fun x y => by
        funext i
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker (L.domRestrict W) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun]
    exact hWj
  obtain ⟨w, hwker, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0 : (w : Fin N → ℂ) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hL0 : ∀ i : Fin j, ∑ n, (w : Fin N → ℂ) n *
      (W8 (Φ (Fin.castLE (le_of_lt j.2) i)) (probe ((n : ℝ) + 7)) : ℂ) = 0 := fun i =>
    congrFun (LinearMap.mem_ker.mp hwker) i
  have hneg : hermQuad M (w : Fin N → ℂ) < 0 := by
    have h := hWpos (w : Fin N → ℂ) w.2 hv0
    rw [hermQuad_neg] at h
    linarith
  have hreal : ∀ a b, (M a b).im = 0 := fun a b => Complex.ofReal_im _
  rw [hermQuad_eq_re_add_im hreal, hermQuad_confinedProbeGram_ofReal,
    hermQuad_confinedProbeGram_ofReal] at hneg
  have hcon : ∀ i : Fin (k + 1), i < j → ∀ v : Fin N → ℝ,
      (∑ n, (v n : ℂ) * (W8 (Φ i) (probe ((n : ℝ) + 7)) : ℂ)) = 0 →
      W8 (Φ i) (probeSum (fun k : Fin N => (k : ℝ) + 7) v) = 0 := by
    intro i _ v hvz
    rw [exponentialPair_probeSum (hD i)]
    exact_mod_cast hvz
  have hcast : ∀ i : Fin (k + 1), (hij : i < j) →
      Fin.castLE (le_of_lt j.2) (⟨(i : ℕ), hij⟩ : Fin j) = i := fun i hij => Fin.ext rfl
  have h1 := hpos (fun n => ((w : Fin N → ℂ) n).re) fun i hij => by
    apply hcon i hij
    have h := congrArg Complex.re (hL0 ⟨i, hij⟩)
    rw [hcast i hij] at h
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.zero_re] at h
    exact_mod_cast h
  have h2 := hpos (fun n => ((w : Fin N → ℂ) n).im) fun i hij => by
    apply hcon i hij
    have h := congrArg Complex.im (hL0 ⟨i, hij⟩)
    rw [hcast i hij] at h
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add, Complex.zero_im] at h
    exact_mod_cast h
  linarith

/-- **At least `j + 1` negative squares beyond the `j`-th rung.** -/
theorem IsCriticalLadder.exists_le_hermNegIndex {k : ℕ} {R : Fin (k + 1) → ℝ}
    {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ) (j : Fin (k + 1)) {r : ℝ}
    (hrj : R j < r) :
    ∃ N : ℕ, (j : ℕ) + 1 ≤ hermNegIndex (confinedProbeGram r (fun i : Fin N => (i : ℝ) + 7)) := by
  have hr : 0 < r := (hL.pos j).trans hrj
  have hle : (j : ℕ) + 1 ≤ k + 1 := Nat.succ_le_of_lt j.2
  set Ψ : Fin ((j : ℕ) + 1) → ℝ → ℝ := fun i => Φ (Fin.castLE hle i) with hΨdef
  set S : Fin ((j : ℕ) + 1) → ℝ := fun i => R (Fin.castLE hle i) with hSdef
  have hΨnull : ∀ i, IsConfinedNullVector (S i) (Ψ i) := fun i => hL.null _
  have hΨorth : ∀ i l, i ≠ l → W8 (Ψ i) (Ψ l) = 0 := fun i l hil =>
    hL.orth _ _ fun h => hil (Fin.castLE_injective hle h)
  have hΨD : ∀ i, CriticalHalfLineEnergyDomain (Ψ i) := fun i => (hΨnull i).1
  have hΨm : ∀ i, (∫ u, Ψ i u ^ 2) ≤ 1 := fun i => (hL.unit _).le
  have hW1 : ∀ i, 1 ≤ W8 (Ψ i) (Ψ i) := fun i => by
    rw [criticalHalfLineExponentialPair_self]
    calc (1 : ℝ) = ∫ u, Ψ i u ^ 2 := (hL.unit _).symm
      _ ≤ ∫ u, Ψ i u ^ 2 * Real.exp (-(8 * u)) := by
          refine integral_mono (hΨD i).sq (hΨD i).exponential fun u => ?_
          show Ψ i u ^ 2 ≤ Ψ i u ^ 2 * Real.exp (-(8 * u))
          rcases le_or_gt 0 u with hu | hu
          · rw [(hΨD i).support u hu]; simp
          · have h1 : 1 ≤ Real.exp (-(8 * u)) := Real.one_le_exp (by linarith)
            nlinarith [sq_nonneg (Ψ i u)]
  set δ := criticalAliasCoefficient (R j) - criticalAliasCoefficient r with hδdef
  have hδ : 0 < δ := by
    rw [hδdef, sub_pos, criticalAliasCoefficient_eq_div (R j), criticalAliasCoefficient_eq_div r]
    exact div_lt_div_of_pos_left (criticalAliasCoefficient_positive one_pos) (hL.pos j) hrj
  have hZ : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) :=
    criticalHalfLineEnergyDomain_of_compact_negative contDiff_const HasCompactSupport.zero
      fun _ _ => rfl
  have hQ0 : Q r (fun _ : ℝ => (0 : ℝ)) = 0 := by
    have h := criticalHalfLineFullEnergy_const_mul r (fun _ : ℝ => (0 : ℝ)) 0
    norm_num at h
    exact h
  have hneg : ∀ t : Fin ((j : ℕ) + 1) → ℝ,
      Q r (fun u => ∑ i, t i * Ψ i u) ≤ -(δ * ∑ i, t i ^ 2) := by
    intro t
    have h := fullEnergy_add_sum_nullVectors r hΨnull hΨorth hZ
      (fun i => criticalHalfLineExponentialPair_zero_right _) t Finset.univ
    simp only [zero_add] at h
    rw [h, hQ0, zero_add, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hSi : S i ≤ R j := hL.mono (Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp i.2))
    have ha : criticalAliasCoefficient (R j) ≤ criticalAliasCoefficient (S i) := by
      rw [criticalAliasCoefficient_eq_div (R j), criticalAliasCoefficient_eq_div (S i)]
      exact div_le_div_of_nonneg_left (criticalAliasCoefficient_positive one_pos).le
        (hL.pos _) hSi
    have hw := hW1 i
    have h1 : (criticalAliasCoefficient r - criticalAliasCoefficient (S i)) * W8 (Ψ i) (Ψ i) ≤
        -δ := by
      have h2 : criticalAliasCoefficient r - criticalAliasCoefficient (S i) ≤ -δ := by
        rw [hδdef]; linarith
      nlinarith
    nlinarith [sq_nonneg (t i)]
  obtain ⟨H, hHw, hHneg⟩ := exists_window_family_of_negative hr hΨD hΨm hδ hneg
  choose A hA0 hAw using hHw
  have hHw' : ∀ i, IsWindowTest (∑ l, A l) (H i) := fun i =>
    (hAw i).mono (Finset.single_le_sum (f := A) (fun l _ => hA0 l) (Finset.mem_univ i))
  obtain ⟨N, c, hc⟩ := exists_pick_family_of_window hr hHw' (half_pos hδ) hHneg
  exact ⟨N, le_hermNegIndex_of_confinedPickForm_neg c hc⟩

/-- **Every rung of the ladder in Pick form.** The `j`-th ratio of a critical ladder is the largest
ratio at which no integer confined Pick matrix `(Q_r(e_m, e_n))_{m, n ≥ 7}` has more than `j`
negative squares. -/
theorem IsCriticalLadder.isGreatest_confinedPick {k : ℕ} {R : Fin (k + 1) → ℝ}
    {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ) (j : Fin (k + 1)) :
    IsGreatest {r : ℝ | 0 < r ∧ ∀ N : ℕ,
      hermNegIndex (confinedProbeGram r (fun i : Fin N => (i : ℝ) + 7)) ≤ j} (R j) := by
  refine ⟨⟨hL.pos j, fun N => hL.hermNegIndex_confinedProbeGram_le j (hL.pos j) le_rfl N⟩,
    fun r ⟨_, hN⟩ => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨N, hN'⟩ := hL.exists_le_hermNegIndex j hlt
  have := hN N
  omega

/-- **The ratios do not depend on the ladder.** -/
theorem IsCriticalLadder.ratio_eq {k k' : ℕ} {R : Fin (k + 1) → ℝ} {Φ : Fin (k + 1) → ℝ → ℝ}
    {R' : Fin (k' + 1) → ℝ} {Φ' : Fin (k' + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ)
    (hL' : IsCriticalLadder k' R' Φ') (j : Fin (k + 1)) (j' : Fin (k' + 1))
    (hjj : (j : ℕ) = j') : R j = R' j' := by
  have h := hL'.isGreatest_confinedPick j'
  rw [← hjj] at h
  exact (hL.isGreatest_confinedPick j).unique h

#print axioms IsCriticalLadder.isGreatest_confinedPick
#print axioms IsCriticalLadder.ratio_eq

end GaloisForLFunctions.ExclusionOfTheCriticalState
