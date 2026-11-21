import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphDissipation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Variational rigidity of finite Fermi–Dirac equilibria

The Fermi–Dirac free energy of Hyun (arXiv:2611.22558) has curvature
at least four in each occupation at unit capacity. On a finite graph
the mass constraint cancels the Gibbs profile's tangent term, leaving
a squared occupation error controlled by the free-energy gap.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

noncomputable section

private def shiftedEntropy (x : ℝ) : ℝ := -Real.binEntropy x - 2 * x ^ 2

private def shiftedEntropySlope (x : ℝ) : ℝ :=
  Real.log x - Real.log (1 - x) - 4 * x

private theorem hasDerivAt_shiftedEntropy {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt shiftedEntropy (shiftedEntropySlope x) x := by
  have hq : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * x) x := by
    have h := ((hasDerivAt_id x).pow 2).const_mul (2 : ℝ)
    change HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * x ^ (2 - 1) * 1)) x at h
    have he : (2 : ℝ) * (2 * x ^ (2 - 1) * 1) = 4 * x := by norm_num [← mul_assoc]
    rw [he] at h
    exact h
  have h := (Real.hasDerivAt_binEntropy hx.1.ne' hx.2.ne).neg.sub hq
  have he : -(Real.log (1 - x) - Real.log x) - 4 * x = shiftedEntropySlope x := by
    unfold shiftedEntropySlope
    ring
  rw [he] at h
  exact h

private theorem hasDerivAt_shiftedEntropySlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt shiftedEntropySlope (1 / x + 1 / (1 - x) - 4) x := by
  have hv : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
  have hlog := hv.log (sub_pos.mpr hx.2).ne'
  have hl : HasDerivAt (fun y : ℝ => 4 * y) 4 x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (4 : ℝ))
  have h := ((Real.hasDerivAt_log hx.1.ne').sub hlog).sub hl
  change HasDerivAt shiftedEntropySlope (x⁻¹ - (-1 / (1 - x)) - 4) x at h
  simpa only [one_div, neg_div, sub_neg_eq_add] using h

private theorem shiftedEntropy_convex : ConvexOn ℝ (Icc 0 1) shiftedEntropy := by
  have hc : Continuous shiftedEntropy := by
    unfold shiftedEntropy
    exact Real.binEntropy_continuous.neg.sub (continuous_const.mul (continuous_id.pow 2))
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := shiftedEntropySlope)
    (f'' := fun x => 1 / x + 1 / (1 - x) - 4) (convex_Icc 0 1) hc.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_shiftedEntropy hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_shiftedEntropySlope hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hpos : 0 < 1 - x := sub_pos.mpr hx.2
    calc
      _ = (2 * x - 1) ^ 2 / (x * (1 - x)) := by
        field_simp [hx.1.ne', hpos.ne']
        ring
      _ ≥ 0 := div_nonneg (sq_nonneg _) (mul_pos hx.1 hpos).le

/-- The entropy lies below its interior tangent by at least twice the
squared occupation change. The comparison point may be an endpoint. -/
theorem binEntropy_quadratic_tangent {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    2 * (y - x) ^ 2 ≤ Real.binEntropy x +
      (Real.log (1 - x) - Real.log x) * (y - x) - Real.binEntropy y := by
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hd := hasDerivAt_shiftedEntropy hx
  have htan : shiftedEntropySlope x * (y - x) ≤ shiftedEntropy y - shiftedEntropy x := by
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have h := shiftedEntropy_convex.le_slope_of_hasDerivAt hx' hy hxy hd
      rw [slope_def_field] at h
      exact (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    · simp
    · have h := shiftedEntropy_convex.slope_le_of_hasDerivAt hy hx' hyx hd
      rw [slope_def_field] at h
      have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
      linarith only [hm]
  unfold shiftedEntropySlope shiftedEntropy at htan
  ring_nf at htan ⊢
  linarith only [htan]

variable {V : Type*} [Fintype V]

/-- Free energy controls squared displacement after its chemical-potential
tangent is subtracted. The comparison field can have vacancies or saturation. -/
theorem freeEnergy_quadratic_tangent (E : V → ℝ) (p : V → Occupation) (x : V → ℝ)
    (hx : ∀ v, x v ∈ Icc (0 : ℝ) 1) :
    2 * ∑ v, (x v - (p v : ℝ)) ^ 2 ≤
      freeEnergy E x - freeEnergy E (fun v => (p v : ℝ)) -
        ∑ v, chemicalPotential E p v * (x v - (p v : ℝ)) := by
  rw [Finset.mul_sum, freeEnergy, freeEnergy, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro v _
  have h := binEntropy_quadratic_tangent (p v).property (hx v)
  have hv : 0 < 1 - (p v : ℝ) := sub_pos.mpr (p v).property.2
  rw [chemicalPotential, Real.log_div (p v).property.1.ne' hv.ne']
  ring_nf at h ⊢
  linarith only [h]

/-- Total occupation of the Gibbs profile. -/
def gibbsMass (E : V → ℝ) (μ : ℝ) : ℝ :=
  ∑ v, (gibbsOccupation (E v) μ : ℝ)

/-- A larger chemical potential increases each occupation strictly. -/
theorem gibbsOccupation_strictMono (e : ℝ) :
    StrictMono (fun μ => (gibbsOccupation e μ : ℝ)) := by
  intro a b hab
  change 1 / (1 + Real.exp (e - a)) < 1 / (1 + Real.exp (e - b))
  apply one_div_lt_one_div_of_lt (by positivity)
  exact add_lt_add_right (Real.exp_lt_exp.mpr (sub_lt_sub_left hab e)) _

/-- A nonempty Gibbs profile has strictly increasing total occupation. -/
theorem gibbsMass_strictMono [Nonempty V] (E : V → ℝ) : StrictMono (gibbsMass E) := by
  intro a b hab
  classical
  let v₀ : V := Classical.choice inferInstance
  exact Finset.sum_lt_sum (fun v _ => ((gibbsOccupation_strictMono (E v)) hab).le)
    ⟨v₀, Finset.mem_univ _, gibbsOccupation_strictMono (E v₀) hab⟩

theorem gibbsMass_continuous (E : V → ℝ) : Continuous (gibbsMass E) := by
  apply continuous_finsetSum _
  intro v _
  change Continuous (fun μ : ℝ => 1 / (1 + Real.exp (E v - μ)))
  have hd : Continuous (fun μ : ℝ => 1 + Real.exp (E v - μ)) := by fun_prop
  exact continuous_const.div hd (fun μ => by positivity)

/-- Every interior total mass selects exactly one chemical potential.
The site potentials of the constant occupation bracket it. -/
theorem existsUnique_gibbsMass (E : V → ℝ) {m : ℝ} (hm : m ∈ Ioo 0 (Fintype.card V : ℝ)) :
    ∃! μ : ℝ, gibbsMass E μ = m := by
  classical
  have hN : 0 < (Fintype.card V : ℝ) := hm.1.trans hm.2
  letI : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hN)
  let v₀ : V := Classical.choice inferInstance
  let q : Occupation := ⟨m / Fintype.card V, div_pos hm.1 hN,
    (div_lt_iff₀ hN).mpr (by simpa only [one_mul] using hm.2)⟩
  let θ (v : V) := chemicalPotential E (fun _ => q) v
  let hs : (Finset.univ : Finset V).Nonempty := ⟨v₀, Finset.mem_univ _⟩
  let a := Finset.univ.inf' hs θ
  let b := Finset.univ.sup' hs θ
  have hle (v : V) : a ≤ θ v := Finset.inf'_le θ (Finset.mem_univ v)
  have hge (v : V) : θ v ≤ b := Finset.le_sup' θ (Finset.mem_univ v)
  have hq (v : V) : (gibbsOccupation (E v) (θ v) : ℝ) = q := by
    have h := (chemicalPotential_eq_iff E (fun _ => q) (θ v) v).mp rfl
    exact congrArg Subtype.val h.symm
  have hmass : (∑ _ : V, (q : ℝ)) = m := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [q]
    field_simp [hN.ne']
  have ha : gibbsMass E a ≤ m := by
    rw [← hmass, gibbsMass]
    exact Finset.sum_le_sum fun v _ =>
      ((gibbsOccupation_strictMono (E v)).monotone (hle v)).trans_eq (hq v)
  have hb : m ≤ gibbsMass E b := by
    rw [← hmass, gibbsMass]
    exact Finset.sum_le_sum fun v _ =>
      (hq v).symm.trans_le ((gibbsOccupation_strictMono (E v)).monotone (hge v))
  obtain ⟨μ, _, hμ⟩ := intermediate_value_Icc ((hle v₀).trans (hge v₀))
    (gibbsMass_continuous E).continuousOn (show m ∈ Icc (gibbsMass E a) (gibbsMass E b) from ⟨ha, hb⟩)
  exact ⟨μ, hμ, fun μ' hm' => (gibbsMass_strictMono E).injective (hm'.trans hμ.symm)⟩

/-- At fixed mass the Gibbs tangent cancels, giving a squared-error
bound for every field in the closed occupation interval. -/
theorem freeEnergy_gibbs_gap (E : V → ℝ) (μ : ℝ) {x : V → ℝ}
    (hx : ∀ v, x v ∈ Icc (0 : ℝ) 1) (hm : (∑ v, x v) = gibbsMass E μ) :
    2 * ∑ v, (x v - (gibbsOccupation (E v) μ : ℝ)) ^ 2 ≤
      freeEnergy E x - freeEnergy E (fun v => (gibbsOccupation (E v) μ : ℝ)) := by
  have h := freeEnergy_quadratic_tangent E (fun v => gibbsOccupation (E v) μ) x hx
  simp only [chemicalPotential_gibbs] at h
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hm, gibbsMass, sub_self, mul_zero, sub_zero] at h
  exact h

/-- The only field at the Gibbs energy and mass is the Gibbs field itself. -/
theorem freeEnergy_eq_gibbs_iff (E : V → ℝ) (μ : ℝ) {x : V → ℝ}
    (hx : ∀ v, x v ∈ Icc (0 : ℝ) 1) (hm : (∑ v, x v) = gibbsMass E μ) :
    freeEnergy E x = freeEnergy E (fun v => (gibbsOccupation (E v) μ : ℝ)) ↔
      x = fun v => (gibbsOccupation (E v) μ : ℝ) := by
  constructor
  · intro he
    have hg := freeEnergy_gibbs_gap E μ hx hm
    rw [he, sub_self] at hg
    have hs : (∑ v, (x v - (gibbsOccupation (E v) μ : ℝ)) ^ 2) = 0 := by
      have hn := Finset.sum_nonneg fun v (_ : v ∈ (Finset.univ : Finset V)) =>
        sq_nonneg (x v - (gibbsOccupation (E v) μ : ℝ))
      linarith only [hg, hn]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => sq_nonneg
      (x v - (gibbsOccupation (E v) μ : ℝ)))).mp hs
    funext v
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hz v (Finset.mem_univ v)))
  · rintro rfl
    rfl

/-- For each interior mass, the Gibbs profile uniquely minimizes free
energy over all occupation fields, including fields on the boundary. -/
theorem existsUnique_fixedMass_freeEnergy_minimizer (E : V → ℝ) {m : ℝ}
    (hm : m ∈ Ioo 0 (Fintype.card V : ℝ)) :
    ∃! x : V → ℝ, (∀ v, x v ∈ Icc (0 : ℝ) 1) ∧ (∑ v, x v) = m ∧
      ∀ y : V → ℝ, (∀ v, y v ∈ Icc (0 : ℝ) 1) → (∑ v, y v) = m →
        freeEnergy E x ≤ freeEnergy E y := by
  obtain ⟨μ, hμ, _⟩ := existsUnique_gibbsMass E hm
  let q (v : V) := (gibbsOccupation (E v) μ : ℝ)
  have hq (v : V) : q v ∈ Icc (0 : ℝ) 1 :=
    ⟨(gibbsOccupation (E v) μ).property.1.le, (gibbsOccupation (E v) μ).property.2.le⟩
  have hmin (y : V → ℝ) (hy : ∀ v, y v ∈ Icc (0 : ℝ) 1) (hym : (∑ v, y v) = m) :
      freeEnergy E q ≤ freeEnergy E y := by
    have hg := freeEnergy_gibbs_gap E μ hy (hym.trans hμ.symm)
    have hn : 0 ≤ ∑ v, (y v - q v) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith only [hg, hn]
  refine ⟨q, ⟨hq, hμ, hmin⟩, ?_⟩
  rintro x ⟨hx, hxm, hbest⟩
  apply (freeEnergy_eq_gibbs_iff E μ hx (hxm.trans hμ.symm)).mp
  exact le_antisymm (hbest q hq hμ) (hmin x hx hxm)

/-- On a connected graph, an interior occupation is stationary exactly
when it minimizes free energy among all fields of the same mass. -/
theorem stationary_iff_fixedMass_freeEnergy_minimizer (G : WeightedGraph V) (E : V → ℝ)
    (p : V → Occupation) (v₀ : V)
    (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) v₀ v) :
    (∀ v, drift G E p v = 0) ↔
      ∀ x : V → ℝ, (∀ v, x v ∈ Icc (0 : ℝ) 1) → (∑ v, x v) = (∑ v, (p v : ℝ)) →
        freeEnergy E (fun v => (p v : ℝ)) ≤ freeEnergy E x := by
  constructor
  · intro h
    obtain ⟨μ, rfl⟩ := (stationary_iff_gibbs_of_paths G E p v₀ hpath).mp h
    intro x hx hm
    have hg := freeEnergy_gibbs_gap E μ hx hm
    exact sub_nonneg.mp ((mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans hg)
  · intro hmin
    let x (v : V) := (p v : ℝ)
    let m := ∑ v, x v
    have hx (v : V) : x v ∈ Icc (0 : ℝ) 1 := ⟨(p v).property.1.le, (p v).property.2.le⟩
    have hm : m ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ) := by
      constructor
      · have h := Finset.sum_lt_sum (s := Finset.univ) (f := fun _ : V => (0 : ℝ)) (g := x)
          (fun v _ => (hx v).1) ⟨v₀, Finset.mem_univ _, (p v₀).property.1⟩
        simpa only [Finset.sum_const_zero] using h
      · have h := Finset.sum_lt_sum (s := Finset.univ) (f := x) (g := fun _ : V => (1 : ℝ))
          (fun v _ => (hx v).2) ⟨v₀, Finset.mem_univ _, (p v₀).property.2⟩
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h
    obtain ⟨μ, hμ, _⟩ := existsUnique_gibbsMass E hm
    let q (v : V) := (gibbsOccupation (E v) μ : ℝ)
    have hq (v : V) : q v ∈ Icc (0 : ℝ) 1 :=
      ⟨(gibbsOccupation (E v) μ).property.1.le, (gibbsOccupation (E v) μ).property.2.le⟩
    have hg := freeEnergy_gibbs_gap E μ hx hμ.symm
    have hge : freeEnergy E q ≤ freeEnergy E x :=
      sub_nonneg.mp ((mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans hg)
    have he : x = q :=
      (freeEnergy_eq_gibbs_iff E μ hx hμ.symm).mp (le_antisymm (hmin q hq hμ) hge)
    have hp : p = fun v => gibbsOccupation (E v) μ :=
      funext fun v => Subtype.ext (congrFun he v)
    rw [hp]
    exact drift_gibbs_eq_zero G E μ

#print axioms binEntropy_quadratic_tangent
#print axioms freeEnergy_quadratic_tangent
#print axioms existsUnique_gibbsMass
#print axioms freeEnergy_gibbs_gap
#print axioms freeEnergy_eq_gibbs_iff
#print axioms existsUnique_fixedMass_freeEnergy_minimizer
#print axioms stationary_iff_fixedMass_freeEnergy_minimizer

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
