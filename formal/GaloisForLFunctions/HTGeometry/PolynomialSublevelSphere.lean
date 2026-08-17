import GaloisForLFunctions.HTGeometry.PolynomialSublevelSlicing

/-!
# The shell mass of a polynomial sublevel set

A homogeneous polynomial scales by the degree power along rays, so the cone over the set where it is
small on the unit shell is contained in the sublevel set of the same polynomial inside the unit box.
The slicing bound therefore turns the shell mass of a sublevel set into a constant times
`ε ^ (1/d)`: a nonzero homogeneous polynomial of degree `d` cannot be small on more than that
fraction of the shell.

This is the elementary, root-factorisation route to a power-law sublevel estimate: no stratification
and no Łojasiewicz exponent, only the top form and one direction in which it does not vanish.
-/

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}


theorem eval_smul_of_isHomogeneous {P : MvPolynomial (Fin m) ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) (r : ℝ) (x : Fin m → ℝ) :
    MvPolynomial.eval (fun i => r * x i) P = r ^ d * MvPolynomial.eval x P := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg : Finsupp.degree u = d := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hu) (hP.coeff_eq_zero hne)
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.prod, Finsupp.prod]
  have hprod : ∏ i ∈ u.support, (r * x i) ^ (u i)
      = r ^ (Finsupp.degree u) * ∏ i ∈ u.support, (x i) ^ (u i) := by
    rw [degree_eq_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (mul_pow _ _ _)
  rw [hprod, hdeg]
  ring

/-- **The ambient sublevel bound.**  On any measurable set whose shear preimage has transverse
projection inside `S`, the sublevel set of a polynomial has measure at most `|v₀|` times the
transverse measure times the one-variable bound. -/
theorem volume_sublevel_le_of_direction {d : ℕ} (hd : 0 < d) (p : MvPolynomial (Fin (m + 1)) ℝ)
    (hp : p.totalDegree ≤ d) (v : Fin (m + 1) → ℝ) (hv0 : v 0 ≠ 0)
    (hc : MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) (A : Set (Fin (m + 1) → ℝ)) (hA : MeasurableSet A)
    (S : Set (Fin m → ℝ)) (hS : MeasurableSet S)
    (hcover : ∀ q : (Fin m → ℝ) × ℝ, Fin.cons 0 q.1 + q.2 • v ∈ A → q.1 ∈ S) :
    volume {x ∈ A | |MvPolynomial.eval x p| ≤ ε}
      ≤ ENNReal.ofReal |v 0| * (volume S * ENNReal.ofReal (2 * d *
          (ε / |MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p)|) ^ ((1 : ℝ) / d))) := by
  classical
  have hcont : Continuous fun x : Fin (m + 1) → ℝ => MvPolynomial.eval x p :=
    MvPolynomial.continuous_eval p
  set A' : Set (Fin (m + 1) → ℝ) := {x ∈ A | |MvPolynomial.eval x p| ≤ ε} with hA'def
  have hA' : MeasurableSet A' :=
    hA.inter (measurableSet_le hcont.abs.measurable measurable_const)
  have hshear := volume_shear_preimage v hv0 A' hA'
  have hsub : {q : (Fin m → ℝ) × ℝ | Fin.cons 0 q.1 + q.2 • v ∈ A'}
      ⊆ {q : (Fin m → ℝ) × ℝ | q.1 ∈ S ∧
          |MvPolynomial.eval (fun i => (Fin.cons (0 : ℝ) q.1 : Fin (m + 1) → ℝ) i + q.2 * v i) p| ≤ ε} := by
    rintro q ⟨hq1, hq2⟩
    refine ⟨hcover q hq1, ?_⟩
    have hpt : (fun i => (Fin.cons (0 : ℝ) q.1 : Fin (m + 1) → ℝ) i + q.2 * v i)
        = Fin.cons 0 q.1 + q.2 • v := by
      funext i
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpt]
    exact hq2
  have hbound := volume_prod_sublevel_le hd p hp v hc hε (b := fun x' : Fin m → ℝ => Fin.cons 0 x')
    (by fun_prop) S hS
  have hchain : (volume : Measure ((Fin m → ℝ) × ℝ))
      {q | Fin.cons 0 q.1 + q.2 • v ∈ A'}
      ≤ volume S * ENNReal.ofReal (2 * d *
          (ε / |MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p)|) ^ ((1 : ℝ) / d)) :=
    le_trans (measure_mono hsub) hbound
  have hpos : (0 : ℝ) < |v 0| := abs_pos.mpr hv0
  have hcancel : ENNReal.ofReal |v 0| * ENNReal.ofReal |(v 0)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hpos), abs_inv, mul_inv_cancel₀ (ne_of_gt hpos),
      ENNReal.ofReal_one]
  calc volume A' = ENNReal.ofReal |v 0| * (ENNReal.ofReal |(v 0)⁻¹| * volume A') := by
        rw [← mul_assoc, hcancel, one_mul]
    _ = ENNReal.ofReal |v 0| * (volume : Measure ((Fin m → ℝ) × ℝ))
          {q | Fin.cons 0 q.1 + q.2 • v ∈ A'} := by rw [hshear]
    _ ≤ ENNReal.ofReal |v 0| * (volume S * ENNReal.ofReal (2 * d *
          (ε / |MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p)|) ^ ((1 : ℝ) / d))) := by
        gcongr

theorem continuous_eval_ofLp (P : MvPolynomial (Fin (m + 1)) ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      MvPolynomial.eval (WithLp.ofLp x) P :=
  (MvPolynomial.continuous_eval P).comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).continuous

/-- **The sphere sublevel bound.**  For a nonzero homogeneous polynomial of degree `d`, the shell
mass of the set where it is at most `ε` is at most a finite constant times `ε ^ (1/d)`. -/
theorem exists_toSphere_sublevel_le {d : ℕ} (hd : 0 < d) (P : MvPolynomial (Fin (m + 1)) ℝ)
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      volume.toSphere {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ ε}
        ≤ C * ENNReal.ofReal (ε ^ ((1 : ℝ) / d)) := by
  classical
  obtain ⟨v, hv0, hcv⟩ := exists_direction P hP0
  have htot : P.totalDegree = d := hP.totalDegree hP0
  rw [htot] at hcv
  set c := MvPolynomial.eval v (MvPolynomial.homogeneousComponent d P) with hcdef
  set R : ℝ := 1 + (∑ i, |v i|) / |v 0| with hR
  have hv0pos : (0 : ℝ) < |v 0| := abs_pos.mpr hv0
  have hRpos : 0 < R := by
    have : 0 ≤ (∑ i, |v i|) / |v 0| := by positivity
    linarith
  set S : Set (Fin m → ℝ) := Set.pi Set.univ fun _ => Icc (-R) R with hSdef
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hSvol : volume S ≠ ⊤ := by
    rw [hSdef, volume_pi_pi]
    refine ne_of_lt (ENNReal.prod_lt_top fun i _ => ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  refine ⟨(Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) : ℝ≥0∞) *
      (ENNReal.ofReal |v 0| * (volume S * ENNReal.ofReal (2 * d * (1 / |c|) ^ ((1 : ℝ) / d)))),
    ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hSvol ENNReal.ofReal_ne_top)
  intro ε hε
  set A_ε : Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    {ω | |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ ε} with hAeps
  have hmeasA : MeasurableSet A_ε := by
    have hcont : Continuous fun ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
        |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| :=
      ((continuous_eval_ofLp P).comp continuous_subtype_val).abs
    exact measurableSet_le hcont.measurable measurable_const
  rw [Measure.toSphere_apply' _ hmeasA]
  set Box : Set (Fin (m + 1) → ℝ) := {y | ∀ i, |y i| ≤ 1} with hBox
  have hBoxmeas : MeasurableSet Box := by
    have : Box = ⋂ i : Fin (m + 1), {y : Fin (m + 1) → ℝ | |y i| ≤ 1} := by
      ext y
      simp [hBox]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le ((measurable_pi_apply i).abs) measurable_const
  have hsubmeas : MeasurableSet {y ∈ Box | |MvPolynomial.eval y P| ≤ ε} :=
    hBoxmeas.inter (measurableSet_le (MvPolynomial.continuous_eval P).abs.measurable
      measurable_const)
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' A_ε)
      ⊆ (WithLp.ofLp : EuclideanSpace ℝ (Fin (m + 1)) → (Fin (m + 1) → ℝ)) ⁻¹'
          {y ∈ Box | |MvPolynomial.eval y P| ≤ ε} := by
    rintro x hx
    rw [Set.mem_smul] at hx
    obtain ⟨r, hr, w, hw, rfl⟩ := hx
    obtain ⟨ω, hω, rfl⟩ := hw
    have hnorm : ‖(ω : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hval : |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ ε := hω
    have hcoord : ∀ i, (WithLp.ofLp (r • (ω : EuclideanSpace ℝ (Fin (m + 1))))) i
        = r * (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i := fun i => rfl
    refine ⟨?_, ?_⟩
    · intro i
      rw [hcoord i, abs_mul, abs_of_pos hr.1]
      have hi : |(WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i| ≤ 1 := by
        have := PiLp.norm_apply_le (ω : EuclideanSpace ℝ (Fin (m + 1))) i
        rw [hnorm] at this
        simpa [Real.norm_eq_abs] using this
      nlinarith [hr.1, hr.2, abs_nonneg ((WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i)]
    · have hfun : (WithLp.ofLp (r • (ω : EuclideanSpace ℝ (Fin (m + 1)))))
          = fun i => r * (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) i := by
        funext i
        exact hcoord i
      rw [hfun, eval_smul_of_isHomogeneous hP, abs_mul, abs_pow, abs_of_pos hr.1]
      have hrd : r ^ d ≤ 1 := pow_le_one₀ (le_of_lt hr.1) (le_of_lt hr.2)
      nlinarith [abs_nonneg (MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P),
        pow_pos hr.1 d]
  have hcover : ∀ q : (Fin m → ℝ) × ℝ, Fin.cons 0 q.1 + q.2 • v ∈ Box → q.1 ∈ S := by
    intro q hq
    have h0 : |q.2| * |v 0| ≤ 1 := by
      have h := hq 0
      have hval : ((Fin.cons (0 : ℝ) q.1 + q.2 • v : Fin (m + 1) → ℝ)) 0 = q.2 * v 0 := by
        simp
      rw [hval, abs_mul] at h
      exact h
    have hq2 : |q.2| ≤ 1 / |v 0| := by
      rw [le_div_iff₀ hv0pos]
      exact h0
    intro j _
    have hj := hq j.succ
    have hval : ((Fin.cons (0 : ℝ) q.1 + q.2 • v : Fin (m + 1) → ℝ)) j.succ
        = q.1 j + q.2 * v j.succ := by
      simp
    rw [hval] at hj
    have habs : |q.1 j| ≤ 1 + |q.2| * |v j.succ| := by
      have h1 : |q.1 j| ≤ |q.1 j + q.2 * v j.succ| + |q.2 * v j.succ| := by
        have h2 := abs_add_le (q.1 j + q.2 * v j.succ) (-(q.2 * v j.succ))
        simpa using h2
      rw [abs_mul] at h1
      linarith
    have hvj : |v j.succ| ≤ ∑ i, |v i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (v i)) (Finset.mem_univ j.succ)
    have hsum : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hfin : |q.1 j| ≤ R := by
      rw [hR]
      have : |q.2| * |v j.succ| ≤ (1 / |v 0|) * (∑ i, |v i|) := by
        refine mul_le_mul hq2 hvj (abs_nonneg _) (by positivity)
      calc |q.1 j| ≤ 1 + |q.2| * |v j.succ| := habs
        _ ≤ 1 + (1 / |v 0|) * (∑ i, |v i|) := by linarith
        _ = 1 + (∑ i, |v i|) / |v 0| := by ring
    exact abs_le.mp hfin
  have hambient := volume_sublevel_le_of_direction hd P (le_of_eq htot) v hv0 hcv hε Box hBoxmeas
    S hS hcover
  have htrans : volume ((WithLp.ofLp : EuclideanSpace ℝ (Fin (m + 1)) → (Fin (m + 1) → ℝ)) ⁻¹'
      {y ∈ Box | |MvPolynomial.eval y P| ≤ ε})
      = volume {y ∈ Box | |MvPolynomial.eval y P| ≤ ε} :=
    (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage hsubmeas.nullMeasurableSet
  have hsplit : ENNReal.ofReal (2 * d * (ε / |c|) ^ ((1 : ℝ) / d))
      = ENNReal.ofReal (2 * d * (1 / |c|) ^ ((1 : ℝ) / d)) * ENNReal.ofReal (ε ^ ((1 : ℝ) / d)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_eq_mul_inv, one_div |c|, Real.mul_rpow hε (by positivity)]
    ring
  calc (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) : ℝ≥0∞) *
        volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A_ε))
      ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) : ℝ≥0∞) *
        volume {y ∈ Box | |MvPolynomial.eval y P| ≤ ε} := by
        gcongr
        rw [← htrans]
        exact measure_mono hcone
    _ ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) : ℝ≥0∞) *
        (ENNReal.ofReal |v 0| * (volume S * ENNReal.ofReal (2 * d * (ε / |c|) ^ ((1 : ℝ) / d)))) := by
        gcongr
    _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) : ℝ≥0∞) *
        (ENNReal.ofReal |v 0| * (volume S *
          ENNReal.ofReal (2 * d * (1 / |c|) ^ ((1 : ℝ) / d)))) * ENNReal.ofReal (ε ^ ((1 : ℝ) / d)) := by
        rw [hsplit]
        ring


/-- **The zero set of a nonzero homogeneous polynomial is shell-null.**  Letting the level tend to
zero in the sublevel bound leaves no mass. -/
theorem toSphere_zeroSet_eq_zero {d : ℕ} (hd : 0 < d) (P : MvPolynomial (Fin (m + 1)) ℝ)
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    volume.toSphere {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P = 0} = 0 := by
  classical
  obtain ⟨C, hCtop, hbound⟩ := exists_toSphere_sublevel_le hd P hP hP0
  set Z : Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    {ω | MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P = 0} with hZ
  have hsub : ∀ ε : ℝ, 0 ≤ ε →
      Z ⊆ {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ ε} := by
    intro ε hε ω hω
    show |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ ε
    have : MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P = 0 := hω
    rw [this, abs_zero]
    exact hε
  have hseq : ∀ n : ℕ,
      volume.toSphere Z ≤ C * ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ ((1 : ℝ) / d)) := by
    intro n
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    exact le_trans (measure_mono (hsub _ hpos)) (hbound _ hpos)
  have hzero : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) ^ ((1 : ℝ) / d))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]
    have hd' : (0 : ℝ) < 1 / d := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
    have hcont := (Real.continuousAt_rpow_const 0 ((1 : ℝ) / d) (Or.inr (le_of_lt hd'))).tendsto
    have hzero0 : (0 : ℝ) ^ ((1 : ℝ) / d) = 0 := Real.zero_rpow (ne_of_gt hd')
    rw [hzero0] at hcont
    exact hcont.comp hbase
  have htend : Filter.Tendsto
      (fun n : ℕ => C * ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ ((1 : ℝ) / d)))
      Filter.atTop (nhds 0) := by
    have hofReal : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ ((1 : ℝ) / d)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hzero
    have := ENNReal.Tendsto.const_mul hofReal (Or.inr hCtop)
    simpa using this
  refine le_antisymm (ge_of_tendsto htend (Filter.Eventually.of_forall hseq)) (by simp)


end

end GaloisForLFunctions.HTGeometry
