import GaloisForLFunctions.GrowingWindowsOfSpecZ.RefiningTheLatticeLowersTheMargin
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# The continuum margin is the dyadic limit

The **orbit correlation** `c_φ(v) = W(φ(· − v), φ)` (`weilOrbitCorr`) is the zero sum
`Re Σ_ρ e^{v(ρ−½)}W_ρ(φ, φ)`, the lag structure of `φ` (SRT, AOG), hence continuous in `v`
(`continuous_weilOrbitCorr`), unconditionally. The Weil sequence of a lattice is its restriction to
`hℤ`.

The **continuum corner margin** of `φ` at length `T` (`contMargin`) is the infimum of Weil's form over
`φ + Σ_i a_iφ(· − s_i)` with finitely many translates `s_i ∈ [−T, 0)` (`cornerCombo`).

* **Translate combinations** (`weilQuad_sum_scaleShift`): `Q(Σ_i b_iφ(· − t_i)) = Σ_{i,j}b_ib_jc_φ(t_i − t_j)`,
  continuous in the translation vector (`continuous_weilQuad_cornerCombo`).
* **The dyadic limit** (`tendsto_levinsonErr_dyadic_contMargin`): under RH, for every nonzero bump,
  step `h > 0` and `n ≥ 1`, `E_{2^jn}(φ, h/2^j) → contMargin(φ, nh)` as `j → ∞`. Lattice margins are
  corner values over dyadic translates; translates are continuous in Weil's form, and dyadic
  translates are dense.

The limit is degenerate: translates arbitrarily close to the corner are admissible, so
`contMargin(φ, T) = 0` under RH (`contMargin_eq_zero`). Lattice canonical systems of a fixed bump
therefore have no unnormalized continuum limit; the continuum invariants are the margins rescaled by
powers of the step (`tendsto_levinsonErr_one_div_sq`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis Zeta23

variable {φ : ℝ → ℝ}

/-! ### The orbit correlation is continuous -/

/-- The **orbit correlation** `c_φ(v) = W(φ(· − v), φ)`. -/
def weilOrbitCorr (φ : ℝ → ℝ) (v : ℝ) : ℝ := weilPair (scaleShift v φ) φ

/-- **The orbit correlation is continuous**: it is the real part of the lag structure of `φ`. -/
theorem continuous_weilOrbitCorr (hφ : φ ∈ realTests) : Continuous (weilOrbitCorr φ) := by
  obtain ⟨w, -, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hφ.2)
  have hbs : ∀ u, cx φ u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra h
    exact hu (hw u (not_le.mp h))
  have hlag := SquareRootThreshold.continuous_lagStructure zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig (cx_contDiff hφ.1) hbs
  have heq : weilOrbitCorr φ = fun v =>
      (SquareRootThreshold.lagStructure zetaZeroConfig (cx φ) v).re := by
    funext v
    have hs := scaleShift_mem v hφ
    rw [ArithmeticOrientationGeometry.lagStructure_eq zetaZeroConfig hφ,
      ArithmeticOrientationGeometry.tsum_exp_Wsummand_eq_W,
      RHTower.zeta_W_eq_weilFullFunctional_mixed (cx_contDiff hs.1) (cx_hasCompactSupport hs.2)
        (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)]
    rfl
  rw [heq]
  exact Complex.continuous_re.comp hlag

/-- Lattice translates are scale shifts. -/
theorem latticeTranslate_eq_scaleShift' (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) :
    latticeTranslate φ h d = scaleShift (-((d : ℝ) * h)) φ := by
  funext u; simp [latticeTranslate, scaleShift]

/-! ### Translate combinations -/

/-- **Weil's form of a translate combination**:
`Q(Σ_i b_iφ(· − t_i)) = Σ_{i,j}b_ib_jc_φ(t_i − t_j)`. -/
theorem weilQuad_sum_scaleShift (hφ : φ ∈ realTests) {M : ℕ} (b t : Fin M → ℝ) :
    weilQuad (∑ i, b i • scaleShift (t i) φ) =
      ∑ i, ∑ j, b i * b j * weilOrbitCorr φ (t i - t j) := by
  have hT : ∀ i, b i • scaleShift (t i) φ ∈ realTests := fun i =>
    Submodule.smul_mem _ _ (scaleShift_mem _ hφ)
  have hS : (∑ i, b i • scaleShift (t i) φ) ∈ realTests := Submodule.sum_mem _ fun i _ => hT i
  show weilPair (∑ i, b i • scaleShift (t i) φ) (∑ i, b i • scaleShift (t i) φ) = _
  rw [weilPair_sum_left _ hT hS]
  refine sum_congr rfl fun i _ => ?_
  rw [weilPair_smul_left, weilPair_comm, weilPair_sum_left _ hT (scaleShift_mem _ hφ), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [weilPair_smul_left, weilPair_comm, weilPair_scaleShift, weilOrbitCorr]
  ring

/-- A **corner combination**: the corner `φ` plus translates `Σ_i a_iφ(· − s_i)`. -/
def cornerCombo (φ : ℝ → ℝ) {m : ℕ} (a s : Fin m → ℝ) : ℝ → ℝ :=
  φ + ∑ i, a i • scaleShift (s i) φ

theorem cornerCombo_eq_sum (φ : ℝ → ℝ) {m : ℕ} (a s : Fin m → ℝ) :
    cornerCombo φ a s = ∑ i : Fin (m + 1),
      (Fin.cons 1 a : Fin (m + 1) → ℝ) i • scaleShift ((Fin.cons 0 s : Fin (m + 1) → ℝ) i) φ := by
  rw [Fin.sum_univ_succ, cornerCombo]
  simp [scaleShift_zero]

/-- **Weil's form of a corner combination is continuous in the translates.** -/
theorem continuous_weilQuad_cornerCombo (hφ : φ ∈ realTests) {m : ℕ} (a : Fin m → ℝ) :
    Continuous fun s : Fin m → ℝ => weilQuad (cornerCombo φ a s) := by
  have hc := continuous_weilOrbitCorr hφ
  have heq : (fun s : Fin m → ℝ => weilQuad (cornerCombo φ a s)) = fun s =>
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (Fin.cons 1 a : Fin (m + 1) → ℝ) i *
        (Fin.cons 1 a : Fin (m + 1) → ℝ) j *
          weilOrbitCorr φ ((Fin.cons 0 s : Fin (m + 1) → ℝ) i - (Fin.cons 0 s : Fin (m + 1) → ℝ) j) := by
    funext s
    rw [cornerCombo_eq_sum, weilQuad_sum_scaleShift hφ]
  rw [heq]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine continuous_const.mul (hc.comp ?_)
  have hcons : ∀ k : Fin (m + 1), Continuous fun s : Fin m → ℝ => (Fin.cons 0 s : Fin (m + 1) → ℝ) k :=
    fun k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Fin.cons_zero]; exact continuous_const
      · simp only [Fin.cons_succ]; exact continuous_apply k
  exact (hcons i).sub (hcons j)

/-- The values of Weil's form on corner combinations with translates in `[−T, 0)`. -/
def cornerValues (φ : ℝ → ℝ) (T : ℝ) : Set ℝ :=
  {v | ∃ (m : ℕ) (a s : Fin m → ℝ), (∀ i, s i ∈ Ico (-T) 0) ∧ v = weilQuad (cornerCombo φ a s)}

/-- The **continuum corner margin** of `φ` at length `T`. -/
def contMargin (φ : ℝ → ℝ) (T : ℝ) : ℝ := sInf (cornerValues φ T)

/-! ### Lattices as corner combinations -/

theorem latticeTest_eq_cornerCombo (φ : ℝ → ℝ) (h : ℝ) {N : ℕ} (a : Fin N → ℝ) :
    latticeTest φ h (Fin.cons 1 a : Fin (N + 1) → ℝ) =
      cornerCombo φ a (fun k => -(((k : ℕ) + 1 : ℝ) * h)) := by
  rw [latticeTest, Fin.sum_univ_succ, cornerCombo]
  simp only [Fin.cons_zero, Fin.cons_succ, one_smul, Fin.val_zero, Nat.cast_zero,
    latticeTranslate_zero, Fin.val_succ]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [latticeTranslate_eq_scaleShift']
  push_cast
  ring_nf

/-- `latticeTest` is additive in the amplitudes. -/
theorem latticeTest_add (φ : ℝ → ℝ) (h : ℝ) {N : ℕ} (x y : Fin N → ℝ) :
    latticeTest φ h (x + y) = latticeTest φ h x + latticeTest φ h y := by
  simp only [latticeTest, Pi.add_apply, add_smul, sum_add_distrib]

theorem latticeTest_smul (φ : ℝ → ℝ) (h : ℝ) {N : ℕ} (c : ℝ) (x : Fin N → ℝ) :
    latticeTest φ h (c • x) = c • latticeTest φ h x := by
  simp only [latticeTest, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem latticeTest_single (φ : ℝ → ℝ) (h : ℝ) {N : ℕ} (k : Fin N) :
    latticeTest φ h (Pi.single k 1) = latticeTranslate φ h k := by
  rw [latticeTest, Fintype.sum_eq_single k fun j hj => by simp [hj]]
  simp

theorem latticeTest_sum (φ : ℝ → ℝ) (h : ℝ) {N m : ℕ} (x : Fin m → Fin N → ℝ) :
    latticeTest φ h (∑ i, x i) = ∑ i, latticeTest φ h (x i) := by
  simp only [latticeTest, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

/-! ### The dyadic limit -/

/-- **The continuum margin is the dyadic limit.** Under RH, for every nonzero bump `φ`, step `h > 0`
and `n ≥ 1`, the margins of the dyadic refinements converge to the continuum corner margin:
`E_{2^jn}(φ, h/2^j) → contMargin(φ, nh)`. -/
theorem tendsto_levinsonErr_dyadic_contMargin (hRH : RiemannHypothesis) (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun j : ℕ => levinsonErr (weilSeq φ (h / 2 ^ j)) (2 ^ j * n)) atTop
      (𝓝 (contMargin φ (n * h))) := by
  set E : ℕ → ℝ := fun j => levinsonErr (weilSeq φ (h / 2 ^ j)) (2 ^ j * n)
  have hpos : ∀ (s : ℝ), 0 < s → ∀ m, 0 < levinsonErr (weilSeq φ s) m := fun s hs m =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 s hs m
  have hanti : Antitone E := levinsonErr_dyadic_antitone hRH hφ hφ0 hh n
  have hbdd : BddBelow (Set.range E) := ⟨0, by rintro _ ⟨j, rfl⟩; exact (hpos _ (by positivity) _).le⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  -- the corner values are nonnegative and contain `Q(φ)`
  have hS0 : ∀ v ∈ cornerValues φ (n * h), 0 ≤ v := by
    rintro v ⟨m, a, s, -, rfl⟩
    have hmem : cornerCombo φ a s ∈ realTests := by
      rw [cornerCombo_eq_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (scaleShift_mem _ hφ)
    exact (ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg.mp hRH)
      _ hmem.1 hmem.2
  have hSne : (cornerValues φ (n * h)).Nonempty :=
    ⟨_, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, rfl⟩
  have hSbdd : BddBelow (cornerValues φ (n * h)) := ⟨0, hS0⟩
  -- each margin is a corner value
  have hmemE : ∀ j, E j ∈ cornerValues φ (n * h) := fun j => by
    set h' := h / 2 ^ j
    have hh' : 0 < h' := by positivity
    obtain ⟨N, hN⟩ : ∃ N, 2 ^ j * n = N := ⟨_, rfl⟩
    have hne : ∀ k < N, levinsonErr (weilSeq φ h') k ≠ 0 := fun k _ => (hpos h' hh' k).ne'
    refine ⟨N, levinsonPred (weilSeq φ h') N, fun k => -(((k : ℕ) + 1 : ℝ) * h'), fun k => ?_, ?_⟩
    · have hk : ((k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
      have hNh : (N : ℝ) * h' = n * h := by
        rw [← hN]; simp only [h']; push_cast; field_simp
      constructor <;> nlinarith
    · simp only [E]
      rw [hN, ← toeplitzForm_levinsonVec (weilSeq_isEven φ h') hne, ← weilQuad_latticeTest hφ,
        levinsonVec, latticeTest_eq_cornerCombo]
  convert hlim using 2
  apply le_antisymm
  · exact le_ciInf fun j => csInf_le hSbdd (hmemE j)
  · refine le_csInf hSne ?_
    rintro v ⟨m, a, s, hs, rfl⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    -- continuity in the translates
    have hcont := (continuous_weilQuad_cornerCombo hφ a).continuousAt (x := s)
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont ε hε
    -- a dyadic step finer than `δ`
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hδ hh) (by norm_num : (1 / 2 : ℝ) < 1)
    set h' := h / 2 ^ j
    have hh' : 0 < h' := by positivity
    have hh'δ : h' < δ := by
      have : h' = h * (1 / 2) ^ j := by simp only [h']; rw [one_div_pow]; ring
      rw [this]
      have := (lt_div_iff₀ hh).mp hj
      linarith
    set N := 2 ^ j * n
    have hNh : (N : ℝ) * h' = n * h := by simp only [N, h']; push_cast; field_simp
    -- round each translate up to the dyadic lattice
    set k : Fin m → ℕ := fun i => ⌈-(s i) / h'⌉₊
    have hk1 : ∀ i, 1 ≤ k i := fun i => by
      have : 0 < -(s i) / h' := div_pos (by linarith [(hs i).2]) hh'
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr this).ne'
    have hkN : ∀ i, k i ≤ N := fun i => by
      refine Nat.ceil_le.mpr ?_
      rw [div_le_iff₀ hh']
      linarith [(hs i).1]
    have hkclose : ∀ i, |(-((k i : ℝ) * h')) - s i| < δ := fun i => by
      have h1 : -(s i) / h' ≤ k i := Nat.le_ceil _
      have h2 : (k i : ℝ) < -(s i) / h' + 1 := Nat.ceil_lt_add_one (div_pos
        (by linarith [(hs i).2]) hh').le
      rw [div_le_iff₀ hh'] at h1
      have h3 : (k i : ℝ) * h' < -(s i) + h' := by
        have := mul_lt_mul_of_pos_right h2 hh'
        rw [add_mul, div_mul_cancel₀ _ hh'.ne', one_mul] at this
        exact this
      rw [abs_lt]; constructor <;> nlinarith
    set s' : Fin m → ℝ := fun i => -((k i : ℝ) * h')
    have hs'close : dist s' s < δ := (dist_pi_lt_iff hδ).mpr fun i => by
      rw [Real.dist_eq]; exact hkclose i
    have hval := hball hs'close
    rw [Real.dist_eq, abs_lt] at hval
    -- the dyadic corner combination is a lattice test with first amplitude `1`
    set x : Fin (N + 1) → ℝ := Pi.single 0 1 + ∑ i, a i • Pi.single ⟨k i, by
      have := hkN i; omega⟩ 1
    have hx0 : x 0 = 1 := by
      simp only [x, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
      rw [Finset.sum_eq_zero fun i _ => by
        rw [if_neg (fun hc => by have := congrArg Fin.val hc; simp at this; have := hk1 i; omega),
          smul_zero]]
      simp
    have hlat : latticeTest φ h' x = cornerCombo φ a s' := by
      simp only [x, latticeTest_add, latticeTest_sum, latticeTest_smul, latticeTest_single,
        cornerCombo, s']
      congr 1
      · rw [show ((0 : Fin (N + 1)) : ℕ) = 0 from rfl]; simp [latticeTranslate_zero]
      · refine sum_congr rfl fun i _ => ?_
        rw [latticeTranslate_eq_scaleShift']
        push_cast
        rfl
    have hxcons : x = Fin.cons 1 (Fin.tail x) := by
      rw [← hx0]; exact (Fin.cons_self_tail x).symm
    have hpd : ToeplitzPosDef (weilSeq φ h') N :=
      toeplitzPosDef_of_riemannHypothesis hRH hφ hφ0 hh' N
    have hEle := levinsonErr_le_toeplitzForm (weilSeq_isEven φ h') hpd
      (fun k _ => (hpos h' hh' k).ne') (Fin.tail x)
    rw [← hxcons, ← weilQuad_latticeTest hφ, hlat] at hEle
    have hinf : ⨅ i, E i ≤ E j := ciInf_le hbdd j
    simp only [E] at hinf
    linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
