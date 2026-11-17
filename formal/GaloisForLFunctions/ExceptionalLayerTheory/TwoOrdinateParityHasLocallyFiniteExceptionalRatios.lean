import GaloisForLFunctions.ExceptionalLayerTheory.ParityAtCoalescingTopOrdinates
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Exceptional ratios of two top ordinates

A positive phase window persists as the ordinates move. For two ordinates, a small
nonzero return of the phase rotation steps across any such window. Dirichlet approximation
then confines the exceptional ratios in each neighborhood to a single rational number.
-/

open Complex Set Filter Topology Matrix
open RHTower RHTower.CCMParityCauchy RHTower.CCMParityTopLayer

namespace GaloisForLFunctions.ExceptionalLayerTheory

noncomputable section

variable {m : ℕ}

private theorem continuous_nodes (δ : ℝ) (i : Fin m ⊕ Fin m) :
    Continuous (fun t : Fin m → ℝ => ccmNodes δ t i) := by
  rcases i with j | j
  · exact continuous_const.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_apply j)))
  · exact continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_apply j)))

private theorem continuous_gram {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun t : Fin m → ℝ => cauchyGram (ccmNodes δ t)) := by
  refine continuous_matrix fun i j => ?_
  refine ((continuous_nodes δ i).add (continuous_nodes δ j)).inv₀ fun t h => ?_
  have hpos := ccmNodes_re_add_pos hδ t i j
  change ccmNodes δ t i + ccmNodes δ t j = 0 at h
  rw [h, Complex.zero_re] at hpos
  exact (lt_irrefl _ hpos)

private theorem continuous_weight (M : Fin m → ℝ) (i : Fin m ⊕ Fin m) :
    Continuous (fun θ : Fin m → ℝ => phaseWeight M θ i) := by
  rcases i with j | j
  · exact continuous_const.mul (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const)))
  · exact continuous_const.mul (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const).neg))

private theorem continuous_norm_at_nodes {X : Type*} [TopologicalSpace X] {δ : ℝ}
    (hδ : 0 < δ) {t : X → Fin m → ℝ} {x : X → Fin m → ℂ}
    (ht : Continuous t) (hx : Continuous x) :
    Continuous (fun p => normForm δ (t p) (x p)) := by
  have hv := continuous_realLift.comp hx
  exact Complex.continuous_re.comp (hv.dotProduct
    (((continuous_gram hδ).comp ht).matrix_mulVec hv))

private theorem continuous_quad_at_nodes {X : Type*} [TopologicalSpace X] {δ : ℝ}
    (hδ : 0 < δ) (M : Fin m → ℝ) {t θ : X → Fin m → ℝ} {x : X → Fin m → ℂ}
    (ht : Continuous t) (hθ : Continuous θ) (hx : Continuous x) :
    Continuous (fun p => quadForm δ (t p) M (θ p) (x p)) := by
  have hv := ((continuous_gram hδ).comp ht).matrix_mulVec (continuous_realLift.comp hx)
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_weight M i).comp hθ).mul (((continuous_apply i).comp hv).pow 2)

/-- Strict parity balance persists under joint perturbations of distinct nodes and phases.
The comparison uses the reference ellipsoid for both perturbed Rayleigh quotients. -/
theorem eventually_positive_parity_at_nodes {δ : ℝ} (hδ : 0 < δ)
    {t θ M : Fin m → ℝ} (ht : Function.Injective t) (hp : ∀ j, 0 < t j)
    (hm : 0 < m) (hF : 0 < ccmParityBalance δ t M θ) :
    ∀ᶠ p : (Fin m → ℝ) × (Fin m → ℝ) in 𝓝 (t, θ),
      Function.Injective p.1 → (∀ j, 0 < p.1 j) → 0 < ccmParityBalance δ p.1 M p.2 := by
  let b := (ccmLambdaMax δ t M θ + ccmLambdaMax δ t M (halfTurn θ)) / 2
  change 0 < ccmLambdaMax δ t M θ - ccmLambdaMax δ t M (halfTurn θ) at hF
  have hb₁ : b < ccmLambdaMax δ t M θ := by dsimp [b]; linarith only [hF]
  have hb₂ : ccmLambdaMax δ t M (halfTurn θ) < b := by dsimp [b]; linarith only [hF]
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht hp hm M θ
  change normForm δ t x = 1 at hx
  have hx0 : x ≠ 0 := fun he => by rw [he, normForm_zero] at hx; exact zero_ne_one hx
  have hlow : ∀ᶠ p : (Fin m → ℝ) × (Fin m → ℝ) in 𝓝 (t, θ),
      b * normForm δ p.1 x < quadForm δ p.1 M p.2 x := by
    apply ContinuousAt.eventually_lt
      ((continuous_const.mul (continuous_norm_at_nodes hδ continuous_fst continuous_const)).continuousAt)
      ((continuous_quad_at_nodes hδ M continuous_fst continuous_snd continuous_const).continuousAt)
    change b * normForm δ t x < quadForm δ t M θ x
    rwa [hx, mul_one, hmax]
  have hhigh : ∀ᶠ p : (Fin m → ℝ) × (Fin m → ℝ) in 𝓝 (t, θ),
      ∀ y ∈ unitLevel δ t, -quadForm δ p.1 M p.2 y < b * normForm δ p.1 y := by
    refine (isCompact_unitLevel hδ ht hp).eventually_forall_of_forall_eventually fun y hy => ?_
    apply ContinuousAt.eventually_lt
      ((continuous_quad_at_nodes hδ M (continuous_fst.comp continuous_fst)
        (continuous_snd.comp continuous_fst) continuous_snd).neg.continuousAt)
      ((continuous_const.mul (continuous_norm_at_nodes hδ
        (continuous_fst.comp continuous_fst) continuous_snd)).continuousAt)
    change normForm δ t y = 1 at hy
    have hle := quadForm_le_lambdaMax_mul hδ ht hp hm M (halfTurn θ) y
    rw [quadForm_halfTurn, hy, mul_one] at hle
    change -quadForm δ t M θ y < b * normForm δ t y
    rw [hy, mul_one]
    exact hle.trans_lt hb₂
  filter_upwards [hlow, hhigh] with p h₁ h₂ hinj hpos
  have htest := quadForm_le_lambdaMax_mul hδ hinj hpos hm M p.2 x
  have hL := (mul_lt_mul_iff_of_pos_right (normForm_pos hδ hinj hpos hx0)).mp (h₁.trans_le htest)
  obtain ⟨y, hy, hymax, -⟩ := exists_isMaxOn_quadForm hδ hinj hpos hm M (halfTurn p.2)
  change normForm δ p.1 y = 1 at hy
  have hy0 : y ≠ 0 := fun he => by rw [he, normForm_zero] at hy; exact zero_ne_one hy
  have hNy := normForm_pos hδ ht hp hy0
  let c := (Real.sqrt (normForm δ t y))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.2 hNy)
  have hz : (fun j => (c : ℂ) * y j) ∈ unitLevel δ t := by
    change normForm δ t _ = 1
    rw [normForm_smul]
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hNy.le, inv_mul_cancel₀ hNy.ne']
  have h := h₂ _ hz
  rw [quadForm_real_smul, normForm_smul, hy, mul_one, ← mul_neg, mul_comm b] at h
  have hU := (mul_lt_mul_iff_of_pos_left (sq_pos_of_pos hc)).mp h
  rw [← quadForm_halfTurn, hymax] at hU
  exact sub_pos.mpr (hU.trans hL)

private theorem exists_positive_phase {δ : ℝ} (hδ : 0 < δ) {t M : Fin m → ℝ}
    (ht : Function.Injective t) (hp : ∀ j, 0 < t j) (hm : 0 < m) (hM : ∀ j, 0 < M j) :
    ∃ θ, 0 < ccmParityBalance δ t M θ := by
  obtain ⟨a, -, hno⟩ := ccm_exists_large_aperture_no_symmetric_matrix_pair hδ ht hp
    (fun j => (hM j).ne') 0
  simp only [parityMatrix, apertureWeight_ccm_eq_phaseWeight] at hno
  let θ := aperturePhase t a
  have h := ccmParityBalance_ne_zero hδ ht hp hm (fun j => (hM j).ne') θ hno
  rcases h.lt_or_gt with hn | hp'
  · exact ⟨halfTurn θ, by rw [ccmParityBalance_halfTurn]; exact neg_pos.mpr hn⟩
  · exact ⟨θ, hp'⟩

/-- The two ordinates with first coordinate `r` and ratio `u`. -/
def ordinatePair (r u : ℝ) : Fin 2 → ℝ := ![r, r * u]

private theorem pair_injective {r u : ℝ} (hr : 0 < r) (hu : u ≠ 1) :
    Function.Injective (ordinatePair r u) := by
  have hne : r ≠ r * u := by
    intro h
    apply hu
    apply mul_left_cancel₀ hr.ne'
    simpa only [mul_one] using h.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [ordinatePair]

private theorem pair_positive {r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    ∀ j, 0 < ordinatePair r u j := by
  intro j
  fin_cases j
  · exact hr
  · exact mul_pos hr hu

/-- A nonzero rotation step shorter than the window reaches a lift of the desired phase,
with the first phase fixed exactly. -/
private theorem hit_phase_by_small_step {r u η : ℝ} (hr : 0 < r)
    (θ : Fin 2 → ℝ) (q : ℕ) (k : ℤ)
    (hd : (q : ℝ) * u - k ≠ 0) (hη : |2 * Real.pi * ((q : ℝ) * u - k)| < η) :
    ∃ (a : ℝ) (φ : Fin 2 → ℝ) (z : Fin 2 → ℤ),
      dist φ θ < η ∧ ∀ j, aperturePhase (ordinatePair r u) a j - φ j = z j * (2 * Real.pi) := by
  let d := 2 * Real.pi * ((q : ℝ) * u - k)
  have hd' : d ≠ 0 := mul_ne_zero (by positivity) hd
  let x := (θ 1 - u * θ 0) / d
  let n := ⌊x⌋
  let a := -(θ 0 + ((q : ℝ) * n) * (2 * Real.pi)) / (2 * r)
  let φ : Fin 2 → ℝ := ![θ 0, u * θ 0 + (n : ℝ) * d]
  have hrem : φ 1 - θ 1 = -(Int.fract x * d) := by
    change u * θ 0 + (⌊x⌋ : ℝ) * d - θ 1 = -(Int.fract x * d)
    rw [Int.fract]
    have hx : x * d = θ 1 - u * θ 0 := div_mul_cancel₀ _ hd'
    linarith only [hx, sub_mul x (⌊x⌋ : ℝ) d]
  have ha : -2 * r * a = θ 0 + ((q : ℝ) * n) * (2 * Real.pi) := by
    dsimp [a]
    field_simp
  refine ⟨a, φ, ![(q : ℤ) * n, k * n], ?_, ?_⟩
  · apply (dist_pi_lt_iff (lt_of_le_of_lt (abs_nonneg _) hη)).mpr
    intro j
    fin_cases j
    · simpa [φ] using lt_of_le_of_lt (abs_nonneg _) hη
    · change dist (φ 1) (θ 1) < η
      rw [Real.dist_eq, hrem, abs_neg, abs_mul, abs_of_nonneg (Int.fract_nonneg x)]
      have hle := mul_le_mul_of_nonneg_right (Int.fract_lt_one x).le (abs_nonneg d)
      exact (hle.trans_eq (one_mul _)).trans_lt hη
  · intro j
    fin_cases j
    · change -2 * r * a - θ 0 = (((q : ℤ) * n : ℤ) : ℝ) * _
      rw [ha]
      push_cast
      ring
    · change -2 * (r * u) * a - (u * θ 0 + (n : ℝ) * d) = ((k * n : ℤ) : ℝ) * _
      rw [show -2 * (r * u) * a = u * (-2 * r * a) by ring, ha]
      dsimp [d]
      push_cast
      ring

/-- Ratios of distinct positive ordinates whose aperture line misses strict positive balance. -/
def exceptionalParityRatios (δ r : ℝ) (M : Fin 2 → ℝ) : Set ℝ :=
  {u | 0 < u ∧ u ≠ 1 ∧ ∀ a, ccmParityBalance δ (ordinatePair r u) M
    (aperturePhase (ordinatePair r u) a) ≤ 0}

private theorem locally_single_ratio {δ r u : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hu : 0 < u)
    {M : Fin 2 → ℝ} (hM : ∀ j, 0 < M j) :
    ∃ (k : ℤ) (q : ℕ), 0 < q ∧ ∀ᶠ v in 𝓝 u,
      v ∈ exceptionalParityRatios δ r M → v = k / (q : ℝ) := by
  by_cases he : u = 1
  · subst u
    obtain ⟨a, ε, hε, hwin⟩ := exists_aperture_positive_of_concentrated_ordinates hδ hr
    refine ⟨1, 1, Nat.zero_lt_one, ?_⟩
    have hclose : ∀ᶠ v in 𝓝 (1 : ℝ), |r * v - r| < ε :=
      ContinuousAt.eventually_lt (f := fun v : ℝ => |r * v - r|) (g := fun _ => ε)
        (((continuous_const.mul continuous_id).sub continuous_const).abs.continuousAt)
        continuousAt_const (by simpa using hε)
    filter_upwards [hclose] with v hv ⟨hvpos, hvne, hfail⟩
    have hgap : (∑ j, M j * |ordinatePair r v j - r|) < ε * ∑ j, M j := by
      simp only [Fin.sum_univ_two, ordinatePair, Matrix.cons_val_zero, Matrix.cons_val_one,
        sub_self, abs_zero, mul_zero, zero_add]
      have hs := mul_lt_mul_of_pos_left hv (hM 1)
      nlinarith only [hs, mul_pos hε (hM 0)]
    exact False.elim ((hfail a).not_gt
      (hwin _ M (pair_injective hr hvne) (pair_positive hr hvpos) (by decide) hM hgap))
  obtain ⟨θ, hθ⟩ := exists_positive_phase hδ (pair_injective hr he) (pair_positive hr hu)
    (by decide) hM
  have hpair : Continuous (ordinatePair r) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_const.mul continuous_id
  have hmap : Continuous (fun p : ℝ × (Fin 2 → ℝ) => (ordinatePair r p.1, p.2)) :=
    (hpair.comp continuous_fst).prodMk continuous_snd
  have hev := hmap.continuousAt (x := (u, θ)) (eventually_positive_parity_at_nodes hδ
    (pair_injective hr he) (pair_positive hr hu) (by decide) hθ)
  obtain ⟨η, hη, hbox⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨Q, hQ⟩ := exists_nat_one_div_lt (div_pos hη (by positivity : 0 < 2 * Real.pi))
  obtain ⟨q, hq, -, hret⟩ := HTGeometry.exists_simultaneous_dirichlet
    (fun _ : Fin 1 => u) (Q := Q + 1) (Nat.succ_pos _)
  obtain ⟨k, hk⟩ := hret 0
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hkη : |2 * Real.pi * ((q : ℝ) * u - k)| < η := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [← lt_div_iff₀' (by positivity : 0 < 2 * Real.pi)]
    exact hk.trans (by simpa using hQ)
  have hstep : ∀ᶠ v in 𝓝 u, |2 * Real.pi * ((q : ℝ) * v - k)| < η :=
    ContinuousAt.eventually_lt
      ((continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const)).abs.continuousAt)
      continuousAt_const hkη
  refine ⟨k, q, by omega, ?_⟩
  filter_upwards [hstep, Metric.ball_mem_nhds u hη] with v hv hvη hbad
  obtain ⟨hvpos, hvne, hfail⟩ := hbad
  by_contra heq
  have hd : (q : ℝ) * v - k ≠ 0 := fun h => heq ((eq_div_iff hq'.ne').mpr
    (by rw [mul_comm]; exact sub_eq_zero.mp h))
  obtain ⟨a, φ, z, hφ, hz⟩ := hit_phase_by_small_step hr θ q k hd hv
  have hpos := hbox (y := (v, φ)) (by
    change max (dist v u) (dist φ θ) < η
    exact max_lt hvη hφ) (pair_injective hr hvne) (pair_positive hr hvpos)
  obtain ⟨e, hepos, hφwin⟩ := exists_phase_window_ccmParityBalance_pos hδ (pair_injective hr hvne)
    (pair_positive hr hvpos) (by decide) M φ hpos
  exact (hfail a).not_gt (hφwin _ z fun j => by rw [hz j, sub_self, abs_zero]; exact hepos.le)

/-- At fixed depth, first ordinate and positive masses, each compact subset of the positive
ratio axis contains only finitely many exceptions to positive balance on the aperture line. -/
theorem finite_exceptionalParityRatios_on_compact {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {M : Fin 2 → ℝ} (hM : ∀ j, 0 < M j) {K : Set ℝ} (hK : IsCompact K)
    (hpos : K ⊆ Ioi 0) : (K ∩ exceptionalParityRatios δ r M).Finite := by
  classical
  have hlocal (u : K) : ∃ (c η : ℝ), 0 < η ∧ ∀ v ∈ Metric.ball u.val η,
      v ∈ exceptionalParityRatios δ r M → v = c := by
    obtain ⟨k, q, -, hc⟩ := locally_single_ratio hδ hr (hpos u.property) hM
    obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.mp hc
    exact ⟨k / (q : ℝ), η, hη, fun _ hv => hh hv⟩
  choose c η hη hh using hlocal
  let U (u : K) := Metric.ball u.val (η u)
  obtain ⟨s, hs⟩ := isCompact_iff_finite_subcover.mp hK U (fun _ => Metric.isOpen_ball)
    (fun v hv => Set.mem_iUnion.mpr ⟨⟨v, hv⟩, Metric.mem_ball_self (hη _)⟩)
  refine (s.finite_toSet.image c).subset fun v hv => ?_
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (hs hv.1)
  obtain ⟨hus, huv⟩ := Set.mem_iUnion.mp hu
  exact ⟨u, hus, (hh u v huv hv.2).symm⟩

/-- Every exceptional pair is commensurate. -/
theorem rational_of_mem_exceptionalParityRatios {δ r u : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {M : Fin 2 → ℝ} (hM : ∀ j, 0 < M j) (hu : u ∈ exceptionalParityRatios δ r M) :
    ∃ (k : ℤ) (q : ℕ), 0 < q ∧ u = k / (q : ℝ) := by
  obtain ⟨k, q, hq, h⟩ := locally_single_ratio hδ hr hu.1 hM
  exact ⟨k, q, hq, h.self_of_nhds hu⟩

/-- Outside a finite set of ratios in a compact positive range, every two-ordinate top
layer with the prescribed masses forces odd ground states at arbitrarily large apertures. -/
theorem two_ordinate_ground_odd_outside_finite_set {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {M : Fin 2 → ℝ} (hM : ∀ j, 0 < M j) {K : Set ℝ} (hK : IsCompact K)
    (hpos : K ⊆ Ioi 0) : ∃ E : Finset ℝ, ∀ u ∈ K, u ∉ E →
      ∀ h : FiniteTopLayer δ (ordinatePair r u), h.mult = M →
      ∀ A : ℝ, ∃ a : SuzukiPositiveAperture, A < a.1 ∧ ∀ v : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a v =
          ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 →
          ccmArchimedeanFormReflection a v = -v := by
  classical
  let hf := finite_exceptionalParityRatios_on_compact hδ hr hM hK hpos
  refine ⟨hf.toFinset, fun u hu hout h hmult => ?_⟩
  apply exists_aperture_ground_odd h
  rw [hmult]
  by_contra! hall
  have hne : u ≠ 1 := by
    intro he
    have hc : ordinatePair r u 0 = ordinatePair r u 1 := by simp [ordinatePair, he]
    exact Fin.zero_ne_one (h.injective hc)
  exact hout (hf.mem_toFinset.mpr ⟨hu, hpos hu, hne, hall⟩)

#print axioms rational_of_mem_exceptionalParityRatios
#print axioms two_ordinate_ground_odd_outside_finite_set
#print axioms eventually_positive_parity_at_nodes
#print axioms finite_exceptionalParityRatios_on_compact

end

end GaloisForLFunctions.ExceptionalLayerTheory
