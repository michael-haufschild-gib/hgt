import GaloisForLFunctions.HTGeometry.FirstOrderAlgebraicStripPeriodicity

/-!
# The frequency group of a first-order algebraic almost-periodic strip function is cyclic

A nonconstant holomorphic uniformly almost-periodic strip function `f` satisfying a nonzero implicit
first-order algebraic differential equation `P(f, f') = 0` has a nonzero real period.  Its Bohr
frequency group

`Γ(f) = ⟨ bohrSpectrum (f|ℝ) ⟩`

is therefore contained in the cyclic group `(2π/p)ℤ`; it is nonzero because a nonconstant
almost-periodic function has a nonzero frequency.  Hence `Γ(f) = λℤ` with `λ ≠ 0`, `2π/|λ|` is a
period of `f`, and the frequency rank is exactly one.

Two consequences:

* **Order-one hypertranscendence criterion.**  A uniformly almost-periodic strip function with no
  nonzero real period satisfies no nonzero first-order algebraic differential equation.
* **Factors.**  Every continuous observable of the translates — a function of the restriction of
  `f(· + x)` to the strip — has cyclic frequency group, in particular frequency rank at most one.
-/

open Filter Topology Metric Set Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

/-! ## Bohr coefficients of constants and of periodic functions -/

theorem bohrCoefficient_const_eq_ite (c : ℂ) (lam : ℝ) :
    bohrCoefficient (fun _ : ℝ => c) lam = if lam = 0 then c else 0 := by
  show bohrMean (fun t => c * bohrChar lam t) = _
  rw [bohrMean_const_mul c (continuous_bohrChar lam) (isBohrAlmostPeriodic_bohrChar lam),
    bohrMean_bohrChar]
  split_ifs <;> simp

/-- A frequency carried by a `p`-periodic function lies in `(2π/p)ℤ`. -/
theorem mem_zmultiples_of_bohrCoefficient_ne_zero {F : ℝ → ℂ} (hF : Continuous F) {p : ℝ}
    (hp : 0 < p) (hper : Function.Periodic F p) {lam : ℝ} (hlam : bohrCoefficient F lam ≠ 0) :
    lam ∈ AddSubgroup.zmultiples (2 * Real.pi / p) := by
  have hap := isBohrAlmostPeriodic_of_periodic hp hper
  have htr := bohrCoefficient_comp_add_const hF hap p lam
  have hfun : (fun t => F (t + p)) = F := funext hper
  rw [hfun] at htr
  have hone : expChar lam p = 1 := by
    have h1 : (1 - expChar lam p) * bohrCoefficient F lam = 0 := by linear_combination htr
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hlam)).symm
  rw [expChar, Complex.exp_eq_one_iff] at hone
  obtain ⟨n, hn⟩ := hone
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
  have hre : lam * p = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  rw [zsmul_eq_mul]
  field_simp
  linarith

/-- A continuous bounded almost-periodic function packaged as a bounded continuous function. -/
noncomputable def bcfOfBound {F : ℝ → ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ t, ‖F t‖ ≤ C) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (2 * C) fun s t => by
    have := hC s; have := hC t
    calc dist (F s) (F t) ≤ ‖F s‖ + ‖F t‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * C := by linarith

/-- **Uniqueness, in the form used here.**  Two continuous almost-periodic functions with the same
Bohr coefficients coincide. -/
theorem eq_of_bohrCoefficient_eq_of_continuous {F G : ℝ → ℂ} (hF : Continuous F)
    (hFa : _root_.HTGeometry.IsBohrAlmostPeriodic F) (hG : Continuous G)
    (hGa : _root_.HTGeometry.IsBohrAlmostPeriodic G)
    (h : ∀ lam, bohrCoefficient F lam = bohrCoefficient G lam) : F = G := by
  obtain ⟨CF, hCF⟩ := exists_bound_of_isBohrAlmostPeriodic hF hFa
  obtain ⟨CG, hCG⟩ := exists_bound_of_isBohrAlmostPeriodic hG hGa
  have := eq_of_bohrCoefficient_eq (f := bcfOfBound hF hCF) (g := bcfOfBound hG hCG)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hF hFa)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hG hGa) h
  exact funext this

/-- A nonconstant continuous almost-periodic function carries a nonzero frequency. -/
theorem exists_ne_zero_mem_bohrSpectrum {F : ℝ → ℂ} (hF : Continuous F)
    (hFa : _root_.HTGeometry.IsBohrAlmostPeriodic F) (hnc : ∃ s t : ℝ, F s ≠ F t) :
    ∃ lam : ℝ, lam ≠ 0 ∧ lam ∈ bohrSpectrum F := by
  by_contra hall
  push Not at hall
  obtain ⟨s, t, hst⟩ := hnc
  set c := bohrCoefficient F 0
  have heq := eq_of_bohrCoefficient_eq_of_continuous hF hFa continuous_const
    (isBohrAlmostPeriodic_const c) fun lam => by
      rw [bohrCoefficient_const_eq_ite]
      split_ifs with h
      · rw [h]
      · by_contra hne
        exact hall lam h hne
  exact hst (by rw [heq])

/-! ## Subgroups of a cyclic subgroup of `ℝ` -/

theorem exists_eq_zmultiples_of_le_zmultiples {H : AddSubgroup ℝ} {a : ℝ}
    (hle : H ≤ AddSubgroup.zmultiples a) : ∃ lam : ℝ, H = AddSubgroup.zmultiples lam := by
  obtain ⟨m, hm⟩ := Int.subgroup_cyclic (H.comap (zmultiplesHom ℝ a))
  refine ⟨m • a, le_antisymm (fun h hh => ?_) ?_⟩
  · obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hle hh)
    have hk : k ∈ H.comap (zmultiplesHom ℝ a) := by
      simpa [AddSubgroup.mem_comap, zmultiplesHom_apply] using hh
    rw [hm, AddSubgroup.mem_closure_singleton] at hk
    obtain ⟨j, rfl⟩ := hk
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨j, by rw [smul_eq_mul, mul_smul]⟩
  · rw [AddSubgroup.zmultiples_le]
    have hmem : m ∈ H.comap (zmultiplesHom ℝ a) := by
      rw [hm]; exact AddSubgroup.subset_closure rfl
    simpa [AddSubgroup.mem_comap, zmultiplesHom_apply] using hmem

theorem rank_zmultiples_eq_one {a : ℝ} (ha : a ≠ 0) :
    Module.rank ℤ (AddSubgroup.zmultiples a) = 1 := by
  have hinj : Function.Injective (zmultiplesHom ℝ a) := by
    intro m n h
    simp only [zmultiplesHom_apply] at h
    have h' : ((m : ℝ) - n) * a = 0 := by rw [sub_mul, ← zsmul_eq_mul, ← zsmul_eq_mul, h, sub_self]
    have := (mul_eq_zero.mp h').resolve_right ha
    exact_mod_cast sub_eq_zero.mp this
  have hrange : (zmultiplesHom ℝ a).range = AddSubgroup.zmultiples a := by
    ext x
    simp [AddSubgroup.mem_zmultiples_iff]
  let e : ℤ ≃+ AddSubgroup.zmultiples a :=
    (AddMonoidHom.ofInjective hinj).trans (AddEquiv.addSubgroupCongr hrange)
  rw [← e.toIntLinearEquiv.rank_eq, CommSemiring.rank_self]

/-- A spectrum inside `λℤ` makes `2π/|λ|` a period. -/
theorem periodic_of_bohrSpectrum_subset {F : ℝ → ℂ} (hF : Continuous F)
    (hFa : _root_.HTGeometry.IsBohrAlmostPeriodic F) {lam : ℝ} (hlam : lam ≠ 0)
    (hspec : bohrSpectrum F ⊆ AddSubgroup.zmultiples lam) :
    Function.Periodic F (2 * Real.pi / |lam|) := by
  set P := 2 * Real.pi / |lam|
  have hFP : Continuous fun t => F (t + P) := hF.comp (continuous_id.add continuous_const)
  have hFPa : _root_.HTGeometry.IsBohrAlmostPeriodic fun t => F (t + P) :=
    isBohrAlmostPeriodic_comp_add_const hFa P
  have heq := eq_of_bohrCoefficient_eq_of_continuous hFP hFPa hF hFa fun mu => by
    rw [bohrCoefficient_comp_add_const hF hFa P mu]
    by_cases hmu : bohrCoefficient F mu = 0
    · rw [hmu, mul_zero]
    · obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hspec hmu)
      have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
      have hone : expChar (k • lam) P = 1 := by
        rw [expChar, Complex.exp_eq_one_iff]
        rcases lt_or_gt_of_ne hlam with hneg | hpos
        · refine ⟨-k, ?_⟩
          simp only [P, abs_of_neg hneg, zsmul_eq_mul]
          push_cast
          field_simp
        · refine ⟨k, ?_⟩
          simp only [P, abs_of_pos hpos, zsmul_eq_mul]
          push_cast
          field_simp
      rw [hone, one_mul]
  exact fun t => congrFun heq t

/-! ## The card's theorem -/

/-- **First-order algebraic almost periodicity forces periodicity.**  A nonconstant holomorphic
uniformly almost-periodic function on the strip `|Im z| < η` satisfying a nonzero first-order
algebraic differential equation `P(f, f') = 0` has Bohr frequency group `λℤ` with `λ ≠ 0`, is
periodic with period `2π/|λ|`, and has frequency rank one. -/
theorem firstOrderAlgebraic_stripAlmostPeriodic_frequencyGroup {f : ℂ → ℂ} {η : ℝ} (hη : 0 < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hap : IsImStripUniformlyAlmostPeriodic f η)
    (hnc : ∃ z₁ ∈ imStrip η, ∃ z₂ ∈ imStrip η, f z₁ ≠ f z₂)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0)
    (hrel : ∀ z ∈ imStrip η, relEval P (f z) (deriv f z) = 0) :
    ∃ lam : ℝ, lam ≠ 0 ∧
      AddSubgroup.closure (bohrSpectrum fun x : ℝ => f x) = AddSubgroup.zmultiples lam ∧
      (∀ z ∈ imStrip η, f (z + ((2 * Real.pi / |lam| : ℝ) : ℂ)) = f z) ∧
      Module.rank ℤ (AddSubgroup.closure (bohrSpectrum fun x : ℝ => f x)) = 1 := by
  obtain ⟨p₀, hp₀, hper₀⟩ := exists_real_period_of_firstOrderRelation hη hf hap hnc hP hrel
  -- a positive period
  obtain ⟨p, hp, hper⟩ : ∃ p : ℝ, 0 < p ∧ ∀ z ∈ imStrip η, f (z + p) = f z := by
    rcases lt_or_gt_of_ne hp₀ with hneg | hpos
    · refine ⟨-p₀, by linarith, fun z hz => ?_⟩
      have hz' : z + ((-p₀ : ℝ) : ℂ) ∈ imStrip η := add_ofReal_mem_imStrip hz _
      have := hper₀ _ hz'
      rw [show z + ((-p₀ : ℝ) : ℂ) + (p₀ : ℂ) = z by push_cast; ring] at this
      exact this.symm
    · exact ⟨p₀, hpos, hper₀⟩
  set F : ℝ → ℂ := fun x => f x with hFdef
  have hxS : ∀ x : ℝ, (x : ℂ) ∈ imStrip η := fun x => by simpa [mem_imStrip] using hη
  have hF : Continuous F :=
    continuous_iff_continuousAt.mpr fun x =>
      ((hf.differentiableAt ((isOpen_imStrip η).mem_nhds (hxS x))).continuousAt).comp
        Complex.continuous_ofReal.continuousAt
  have hFper : Function.Periodic F p := fun x => by
    simp only [hFdef]
    push_cast
    exact hper _ (hxS x)
  have hFa := isBohrAlmostPeriodic_of_periodic hp hFper
  -- the restriction to the line is nonconstant
  have hFnc : ∃ s t : ℝ, F s ≠ F t := by
    by_contra hall
    push Not at hall
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hnc
    have hzero := eqOn_zero_of_forall_real (g := fun z => f z - f 0) hη
      (fun z hz => (((hf.analyticOnNhd (isOpen_imStrip η)) z hz).sub analyticAt_const))
      fun x => by simpa [hFdef] using sub_eq_zero.mpr (hall x 0)
    have h1 := hzero hz₁
    have h2 := hzero hz₂
    simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
    exact hne (h1.trans h2.symm)
  -- the frequency group
  have hle : AddSubgroup.closure (bohrSpectrum F) ≤ AddSubgroup.zmultiples (2 * Real.pi / p) :=
    (AddSubgroup.closure_le _).mpr fun lam hlam =>
      mem_zmultiples_of_bohrCoefficient_ne_zero hF hp hFper hlam
  obtain ⟨lam, hlam⟩ := exists_eq_zmultiples_of_le_zmultiples hle
  obtain ⟨mu, hmu, hmuspec⟩ := exists_ne_zero_mem_bohrSpectrum hF hFa hFnc
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    have : mu ∈ AddSubgroup.zmultiples (0 : ℝ) := hlam ▸ AddSubgroup.subset_closure hmuspec
    simp at this
    exact hmu this
  refine ⟨lam, hlam0, hlam, ?_, by rw [hlam]; exact rank_zmultiples_eq_one hlam0⟩
  -- the period `2π/|λ|`
  have hspec : bohrSpectrum F ⊆ AddSubgroup.zmultiples lam := fun x hx =>
    hlam ▸ AddSubgroup.subset_closure hx
  have hFP := periodic_of_bohrSpectrum_subset hF hFa hlam0 hspec
  set Pd := 2 * Real.pi / |lam|
  have hF' : AnalyticOnNhd ℂ f (imStrip η) := hf.analyticOnNhd (isOpen_imStrip η)
  have hshift : AnalyticOnNhd ℂ (fun z => f (z + (Pd : ℂ)) - f z) (imStrip η) := by
    have hd : DifferentiableOn ℂ (fun z => f (z + (Pd : ℂ)) - f z) (imStrip η) :=
      (hf.comp (differentiableOn_id.add_const _) fun z hz => add_ofReal_mem_imStrip hz _).sub hf
    exact hd.analyticOnNhd (isOpen_imStrip η)
  have hzero := eqOn_zero_of_forall_real hη hshift fun x => by
    have := hFP x
    simp only [hFdef] at this
    push_cast at this
    simp [this]
  intro z hz
  have := hzero hz
  simpa [sub_eq_zero] using this

/-- **Order-one hypertranscendence criterion.**  A uniformly almost-periodic holomorphic strip
function without a nonzero real period satisfies no nonzero first-order algebraic differential
equation. -/
theorem exists_relEval_ne_zero_of_not_periodic {f : ℂ → ℂ} {η : ℝ} (hη : 0 < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hap : IsImStripUniformlyAlmostPeriodic f η)
    (hnp : ¬ ∃ p : ℝ, p ≠ 0 ∧ ∀ z ∈ imStrip η, f (z + p) = f z)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) :
    ∃ z ∈ imStrip η, relEval P (f z) (deriv f z) ≠ 0 := by
  by_contra hall
  push Not at hall
  by_cases hnc : ∃ z₁ ∈ imStrip η, ∃ z₂ ∈ imStrip η, f z₁ ≠ f z₂
  · exact hnp (exists_real_period_of_firstOrderRelation hη hf hap hnc hP hall)
  · push Not at hnc
    exact hnp ⟨1, one_ne_zero, fun z hz => hnc _ (add_ofReal_mem_imStrip hz 1) _ hz⟩

/-- **Factors of the translation flow have cyclic frequency group.**  For every observable `Φ` of
the restriction of `f(· + x)` to the strip, if `x ↦ Φ (f(· + x))` is continuous then its frequency
group is cyclic, hence of rank at most one. -/
theorem observable_frequencyGroup_cyclic {f : ℂ → ℂ} {η : ℝ} (hη : 0 < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hap : IsImStripUniformlyAlmostPeriodic f η)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0)
    (hrel : ∀ z ∈ imStrip η, relEval P (f z) (deriv f z) = 0)
    (Φ : (imStrip η → ℂ) → ℂ)
    (hΦ : Continuous fun x : ℝ => Φ fun z : imStrip η => f ((z : ℂ) + x)) :
    ∃ mu : ℝ, AddSubgroup.closure (bohrSpectrum fun x : ℝ => Φ fun z : imStrip η => f ((z : ℂ) + x))
        = AddSubgroup.zmultiples mu ∧
      Module.rank ℤ (AddSubgroup.closure
        (bohrSpectrum fun x : ℝ => Φ fun z : imStrip η => f ((z : ℂ) + x))) ≤ 1 := by
  -- a positive real period of `f` on the strip
  obtain ⟨p, hp, hper⟩ : ∃ p : ℝ, 0 < p ∧ ∀ z ∈ imStrip η, f (z + p) = f z := by
    by_cases hnc : ∃ z₁ ∈ imStrip η, ∃ z₂ ∈ imStrip η, f z₁ ≠ f z₂
    · obtain ⟨p₀, hp₀, hper₀⟩ := exists_real_period_of_firstOrderRelation hη hf hap hnc hP hrel
      rcases lt_or_gt_of_ne hp₀ with hneg | hpos
      · refine ⟨-p₀, by linarith, fun z hz => ?_⟩
        have := hper₀ _ (add_ofReal_mem_imStrip hz (-p₀))
        rw [show z + ((-p₀ : ℝ) : ℂ) + (p₀ : ℂ) = z by push_cast; ring] at this
        exact this.symm
      · exact ⟨p₀, hpos, hper₀⟩
    · push Not at hnc
      exact ⟨1, one_pos, fun z hz => hnc _ (add_ofReal_mem_imStrip hz 1) _ hz⟩
  set h : ℝ → ℂ := fun x => Φ fun z : imStrip η => f ((z : ℂ) + x) with hh
  have hhper : Function.Periodic h p := fun x => by
    simp only [hh]
    congr 1
    funext z
    have := hper _ (add_ofReal_mem_imStrip z.2 x)
    push_cast
    rw [← add_assoc]
    exact this
  have hle : AddSubgroup.closure (bohrSpectrum h) ≤ AddSubgroup.zmultiples (2 * Real.pi / p) :=
    (AddSubgroup.closure_le _).mpr fun lam hlam =>
      mem_zmultiples_of_bohrCoefficient_ne_zero hΦ hp hhper hlam
  obtain ⟨mu, hmu⟩ := exists_eq_zmultiples_of_le_zmultiples hle
  refine ⟨mu, hmu, ?_⟩
  rw [hmu]
  by_cases hmu0 : mu = 0
  · subst hmu0
    have : AddSubgroup.zmultiples (0 : ℝ) = ⊥ := by simp
    rw [this]
    simp
  · rw [rank_zmultiples_eq_one hmu0]

end GaloisForLFunctions.HTGeometry
