import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GibbsVariational

/-!
# Free-energy coercivity for Pauli-blocked transport

Relative particle–hole odds turn the current into a weighted difference
of occupations. The weight stays positive uniformly in the moving
field. Equal mass centers these relative occupations at one half, and
path estimates transfer the Dirichlet bound to the free energy.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace WeightedGraph

variable {V : Type*} [Fintype V]

private theorem edge_sq_le_dirichlet (G : WeightedGraph V) (f : V → ℝ) {v u : V}
    (h : 0 < G.w v u) : (f u - f v) ^ 2 ≤ (2 / G.w v u) * G.dirichlet f f := by
  have hn (a b : V) : 0 ≤ G.w a b * ((f a - f b) * (f a - f b)) :=
    mul_nonneg (G.w_nonneg a b) (mul_self_nonneg _)
  have hrow : G.w v u * ((f v - f u) * (f v - f u)) ≤
      ∑ b, G.w v b * ((f v - f b) * (f v - f b)) :=
    Finset.single_le_sum (fun b _ => hn v b) (Finset.mem_univ u)
  have hsum : (∑ b, G.w v b * ((f v - f b) * (f v - f b))) ≤
      ∑ a, ∑ b, G.w a b * ((f a - f b) * (f a - f b)) :=
    Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg fun b _ => hn a b) (Finset.mem_univ v)
  have he : (f u - f v) ^ 2 * G.w v u = G.w v u * ((f v - f u) * (f v - f u)) := by ring
  rw [show (2 / G.w v u) * G.dirichlet f f = (2 * G.dirichlet f f) / G.w v u by ring]
  apply (le_div_iff₀ h).mpr
  rw [he, dirichlet]
  linarith only [hrow.trans hsum]

/-- Positive edge paths from the root give a uniform anchored Poincaré
bound for every real field. -/
theorem exists_anchored_poincare (G : WeightedGraph V) (root : V)
    (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : V → ℝ, (∑ v, (f v - f root) ^ 2) ≤ C * G.dirichlet f f := by
  have h (v : V) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : V → ℝ, (f v - f root) ^ 2 ≤ C * G.dirichlet f f := by
    induction hpath v with
    | refl => exact ⟨0, le_rfl, fun f => by simp⟩
    | @tail u v _ huv ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨2 * (C + 2 / G.w u v), by positivity, fun f => ?_⟩
      have he := G.edge_sq_le_dirichlet f huv
      have hs : (f v - f root) ^ 2 ≤ 2 * ((f u - f root) ^ 2 + (f v - f u) ^ 2) := by
        nlinarith only [sq_nonneg ((f u - f root) - (f v - f u))]
      exact hs.trans (by linarith only [hbound f, he])
  choose C hC hb using h
  have hc : 0 ≤ ∑ v, C v := Finset.sum_nonneg fun v _ => hC v
  refine ⟨1 + ∑ v, C v, by positivity, fun f => ?_⟩
  calc
    _ ≤ ∑ v, C v * G.dirichlet f f := Finset.sum_le_sum fun v _ => hb v f
    _ = (∑ v, C v) * G.dirichlet f f := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (G.dirichlet_self_nonneg f)

end WeightedGraph

namespace Quantum.FermiGraph

noncomputable section

private theorem vacancy_pos (p : Occupation) : 0 < 1 - (p : ℝ) := sub_pos.mpr p.property.2

/-- The total weight of the two particle–hole factors relative to a reference. -/
def relativeWeight (p q : Occupation) : ℝ :=
  (1 - (p : ℝ)) * (q : ℝ) + (p : ℝ) * (1 - (q : ℝ))

theorem relativeWeight_pos (p q : Occupation) : 0 < relativeWeight p q :=
  add_pos (mul_pos (vacancy_pos p) q.property.1) (mul_pos p.property.1 (vacancy_pos q))

theorem relativeWeight_le_one (p q : Occupation) : relativeWeight p q ≤ 1 := by
  unfold relativeWeight
  have h₀ := mul_le_mul_of_nonneg_left q.property.2.le (vacancy_pos p).le
  have h₁ := mul_le_mul_of_nonneg_left (show 1 - (q : ℝ) ≤ 1 by linarith [q.property.1])
    p.property.1.le
  linarith only [h₀, h₁]

/-- The normalized particle–hole factor equals one half at the reference. -/
def relativeOccupation (p q : Occupation) : Occupation :=
  ⟨(p : ℝ) * (1 - (q : ℝ)) / relativeWeight p q, by
    have h₀ := mul_pos p.property.1 (vacancy_pos q)
    have h₁ := mul_pos (vacancy_pos p) q.property.1
    exact ⟨div_pos h₀ (relativeWeight_pos p q),
      (div_lt_iff₀ (relativeWeight_pos p q)).mpr (by unfold relativeWeight; linarith only [h₁])⟩⟩

private theorem relative_vacancy (p q : Occupation) :
    1 - (relativeOccupation p q : ℝ) = ((1 - (p : ℝ)) * (q : ℝ)) / relativeWeight p q := by
  change 1 - (p : ℝ) * (1 - (q : ℝ)) / relativeWeight p q = _
  field_simp [(relativeWeight_pos p q).ne']
  unfold relativeWeight
  ring

/-- The centered relative occupation recovers the exact signed occupation error. -/
theorem sub_eq_relative_centered (p q : Occupation) :
    (p : ℝ) - (q : ℝ) = 2 * relativeWeight p q * ((relativeOccupation p q : ℝ) - 1 / 2) := by
  change _ = 2 * relativeWeight p q * ((p : ℝ) * (1 - (q : ℝ)) / relativeWeight p q - 1 / 2)
  field_simp [(relativeWeight_pos p q).ne']
  unfold relativeWeight
  ring

private def logOdds (p : Occupation) : ℝ := Real.log ((p : ℝ) / (1 - (p : ℝ)))

private theorem logOdds_eq (p : Occupation) :
    logOdds p = Real.log (p : ℝ) - Real.log (1 - (p : ℝ)) :=
  Real.log_div p.property.1.ne' (vacancy_pos p).ne'

private theorem logOdds_relative (p q : Occupation) :
    logOdds (relativeOccupation p q) = logOdds p - logOdds q := by
  have h : ((relativeOccupation p q : ℝ) / (1 - (relativeOccupation p q : ℝ))) =
      ((p : ℝ) * (1 - (q : ℝ))) / ((1 - (p : ℝ)) * (q : ℝ)) := by
    rw [relative_vacancy]
    change ((p : ℝ) * (1 - (q : ℝ)) / relativeWeight p q) /
      (((1 - (p : ℝ)) * (q : ℝ)) / relativeWeight p q) = _
    field_simp [(relativeWeight_pos p q).ne', (vacancy_pos p).ne', q.property.1.ne']
  unfold logOdds
  rw [h, Real.log_div (mul_pos p.property.1 (vacancy_pos q)).ne'
    (mul_pos (vacancy_pos p) q.property.1).ne',
    Real.log_mul p.property.1.ne' (vacancy_pos q).ne',
    Real.log_mul (vacancy_pos p).ne' q.property.1.ne',
    Real.log_div p.property.1.ne' (vacancy_pos p).ne',
    Real.log_div q.property.1.ne' (vacancy_pos q).ne']
  ring

private theorem logOdds_strong_mono (p q : Occupation) :
    4 * ((p : ℝ) - (q : ℝ)) ^ 2 ≤ (logOdds p - logOdds q) * ((p : ℝ) - (q : ℝ)) := by
  have hp := binEntropy_quadratic_tangent p.property ⟨q.property.1.le, q.property.2.le⟩
  have hq := binEntropy_quadratic_tangent q.property ⟨p.property.1.le, p.property.2.le⟩
  rw [logOdds_eq p, logOdds_eq q]
  nlinarith only [hp, hq]

variable {V : Type*} [Fintype V]

/-- A positive lower bound for all reference occupations and vacancies. -/
def referenceMargin (q : V → Occupation) : ℝ :=
  1 / (1 + ∑ v, (1 / (q v : ℝ) + 1 / (1 - (q v : ℝ))))

omit [Fintype V] in
private theorem referenceReciprocal_nonneg (q : V → Occupation) (v : V) :
    0 ≤ 1 / (q v : ℝ) + 1 / (1 - (q v : ℝ)) :=
  add_nonneg (div_nonneg zero_le_one (q v).property.1.le)
    (div_nonneg zero_le_one (vacancy_pos (q v)).le)

theorem referenceMargin_pos (q : V → Occupation) : 0 < referenceMargin q := by
  unfold referenceMargin
  exact div_pos one_pos (add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun v _ => referenceReciprocal_nonneg q v))

theorem referenceMargin_le (q : V → Occupation) (v : V) :
    referenceMargin q ≤ (q v : ℝ) ∧ referenceMargin q ≤ 1 - (q v : ℝ) := by
  let A := ∑ u, (1 / (q u : ℝ) + 1 / (1 - (q u : ℝ)))
  have hA : 0 ≤ A := Finset.sum_nonneg fun u _ => referenceReciprocal_nonneg q u
  have hs : 1 / (q v : ℝ) + 1 / (1 - (q v : ℝ)) ≤ A :=
    Finset.single_le_sum (fun u _ => referenceReciprocal_nonneg q u) (Finset.mem_univ v)
  have hbound (x : ℝ) (hx : 0 < x) (h : 1 / x ≤ 1 + A) : referenceMargin q ≤ x := by
    change 1 / (1 + A) ≤ x
    exact (div_le_iff₀ (by positivity)).mpr (by
      have he := (div_le_iff₀ hx).mp h
      linarith only [he])
  exact ⟨hbound _ (q v).property.1 (by
    linarith only [hs, div_nonneg zero_le_one (vacancy_pos (q v)).le]),
    hbound _ (vacancy_pos (q v)) (by
      linarith only [hs, div_nonneg zero_le_one (q v).property.1.le])⟩

/-- The relative occupation as a real field on the graph. -/
def relativeField (p q : V → Occupation) : V → ℝ :=
  fun v => relativeOccupation (p v) (q v)

private theorem relativeWeight_div_ge_margin (p q : V → Occupation) (v : V) :
    referenceMargin q ≤ relativeWeight (p v) (q v) / (q v : ℝ) := by
  have h := referenceMargin_le q v
  have h₀ := mul_le_mul_of_nonneg_left h.1 (vacancy_pos (p v)).le
  have h₁ := mul_le_mul_of_nonneg_left h.2 (p v).property.1.le
  have hb : referenceMargin q ≤ relativeWeight (p v) (q v) := by
    unfold relativeWeight
    linarith only [h₀, h₁]
  apply (le_div_iff₀ (q v).property.1).mpr
  exact (mul_le_of_le_one_right (referenceMargin_pos q).le (q v).property.2.le).trans hb

private theorem relativeWeight_product_ge_margin_sq (p q : V → Occupation) (v u : V) :
    referenceMargin q ^ 2 ≤
      (relativeWeight (p v) (q v) / (q v : ℝ)) * (relativeWeight (p u) (q u) / (q u : ℝ)) := by
  have hd := (referenceMargin_pos q).le
  have hv := relativeWeight_div_ge_margin p q v
  rw [pow_two]
  exact mul_le_mul hv (relativeWeight_div_ge_margin p q u) hd (hd.trans hv)

omit [Fintype V] in
private theorem exp_energy_eq (E : V → ℝ) (μ : ℝ) (v : V) :
    let q := gibbsOccupation (E v) μ
    Real.exp (E v) = Real.exp μ * (1 - (q : ℝ)) / (q : ℝ) := by
  let q := gibbsOccupation (E v) μ
  have h := congrArg Real.exp (chemicalPotential_gibbs E μ v)
  rw [chemicalPotential, Real.exp_add, Real.exp_log (div_pos q.property.1 (vacancy_pos q))] at h
  change Real.exp (E v) * ((q : ℝ) / (1 - (q : ℝ))) = Real.exp μ at h
  change Real.exp (E v) = Real.exp μ * (1 - (q : ℝ)) / (q : ℝ)
  rw [← h]
  field_simp [q.property.1.ne', (vacancy_pos q).ne']

omit [Fintype V] in
private theorem chemicalPotential_difference_eq_relative (E : V → ℝ) (μ : ℝ)
    (p : V → Occupation) (v : V) :
    logOdds (relativeOccupation (p v) (gibbsOccupation (E v) μ)) = chemicalPotential E p v - μ := by
  rw [logOdds_relative]
  change _ = (E v + logOdds (p v)) - μ
  have hq : E v + logOdds (gibbsOccupation (E v) μ) = μ := chemicalPotential_gibbs E μ v
  linarith only [hq]

omit [Fintype V] in
/-- The relative field factors the Pauli-blocked current with positive conductances. -/
theorem flux_eq_relativeField (G : WeightedGraph V) (E : V → ℝ) (μ : ℝ)
    (p : V → Occupation) (v u : V) :
    let q := fun a => gibbsOccupation (E a) μ
    flux G E p v u = G.w v u *
      (Real.exp μ * (relativeWeight (p v) (q v) / (q v : ℝ)) *
        (relativeWeight (p u) (q u) / (q u : ℝ))) *
      (relativeField p q v - relativeField p q u) := by
  let q := fun a => gibbsOccupation (E a) μ
  change _ = G.w v u * (Real.exp μ * (relativeWeight (p v) (q v) / (q v : ℝ)) *
      (relativeWeight (p u) (q u) / (q u : ℝ))) * (relativeField p q v - relativeField p q u)
  have hev : Real.exp (E v) = Real.exp μ * (1 - (q v : ℝ)) / (q v : ℝ) := exp_energy_eq E μ v
  have heu : Real.exp (E u) = Real.exp μ * (1 - (q u : ℝ)) / (q u : ℝ) := exp_energy_eq E μ u
  rw [flux_eq_particle_hole, hev, heu]
  change G.w v u *
      ((Real.exp μ * (1 - (q v : ℝ)) / (q v : ℝ)) * (p v : ℝ) * (1 - (p u : ℝ)) -
        (Real.exp μ * (1 - (q u : ℝ)) / (q u : ℝ)) * (p u : ℝ) * (1 - (p v : ℝ))) = _
  unfold relativeField
  change _ = G.w v u * (Real.exp μ * (relativeWeight (p v) (q v) / (q v : ℝ)) *
      (relativeWeight (p u) (q u) / (q u : ℝ))) *
      ((p v : ℝ) * (1 - (q v : ℝ)) / relativeWeight (p v) (q v) -
        (p u : ℝ) * (1 - (q u : ℝ)) / relativeWeight (p u) (q u))
  field_simp [(q v).property.1.ne', (q u).property.1.ne',
    (relativeWeight_pos (p v) (q v)).ne', (relativeWeight_pos (p u) (q u)).ne']
  unfold relativeWeight
  ring

/-- Free-energy dissipation dominates the Dirichlet energy of relative
occupations with a constant independent of the moving field. -/
theorem dissipation_ge_relativeDirichlet (G : WeightedGraph V) (E : V → ℝ) (μ : ℝ)
    (p : V → Occupation) :
    let q := fun v => gibbsOccupation (E v) μ
    let r := relativeField p q
    (4 * (Real.exp μ * referenceMargin q ^ 2)) * G.dirichlet r r ≤ dissipation G E p := by
  let q := fun v => gibbsOccupation (E v) μ
  let r := relativeField p q
  let d := referenceMargin q
  let B (v : V) := relativeWeight (p v) (q v) / (q v : ℝ)
  have hd : 0 < d := referenceMargin_pos q
  have hB (v : V) : d ≤ B v := relativeWeight_div_ge_margin p q v
  have hedge (v u : V) : (4 * (Real.exp μ * d ^ 2)) *
      (G.w v u * ((r v - r u) * (r v - r u))) ≤
      (chemicalPotential E p v - chemicalPotential E p u) * flux G E p v u := by
    have hμ : chemicalPotential E p v - chemicalPotential E p u =
        logOdds (relativeOccupation (p v) (q v)) - logOdds (relativeOccupation (p u) (q u)) := by
      rw [chemicalPotential_difference_eq_relative E μ p v,
        chemicalPotential_difference_eq_relative E μ p u]
      ring
    have hJ : flux G E p v u = G.w v u * (Real.exp μ * B v * B u) * (r v - r u) :=
      flux_eq_relativeField G E μ p v u
    have hlog : 4 * (r v - r u) ^ 2 ≤
        (logOdds (relativeOccupation (p v) (q v)) - logOdds (relativeOccupation (p u) (q u))) *
          (r v - r u) := logOdds_strong_mono _ _
    have hK : Real.exp μ * d ^ 2 ≤ Real.exp μ * B v * B u := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (relativeWeight_product_ge_margin_sq p q v u) (Real.exp_pos μ).le
    have hh (a : V) : 0 ≤ B a := hd.le.trans (hB a)
    have hw : 0 ≤ G.w v u * (Real.exp μ * B v * B u) :=
      mul_nonneg (G.w_nonneg v u) (mul_nonneg (mul_nonneg (Real.exp_pos μ).le (hh v)) (hh u))
    calc
      _ = (G.w v u * (Real.exp μ * d ^ 2)) * (4 * (r v - r u) ^ 2) := by ring
      _ ≤ (G.w v u * (Real.exp μ * B v * B u)) * (4 * (r v - r u) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (G.w_nonneg v u)) (by positivity)
      _ ≤ (G.w v u * (Real.exp μ * B v * B u)) *
          ((logOdds (relativeOccupation (p v) (q v)) - logOdds (relativeOccupation (p u) (q u))) *
            (r v - r u)) := mul_le_mul_of_nonneg_left hlog hw
      _ = _ := by
        rw [hμ, hJ]
        ring
  change (4 * (Real.exp μ * d ^ 2)) * G.dirichlet r r ≤ _
  rw [WeightedGraph.dirichlet, dissipation, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun u _ => hedge v u

/-- Pairing the drift with any test field gives the current paired
with its edge differences. -/
theorem neg_sum_test_mul_drift (G : WeightedGraph V) (E : V → ℝ)
    (p : V → Occupation) (f : V → ℝ) :
    -(∑ v, f v * drift G E p v) = (∑ v, ∑ u, (f v - f u) * flux G E p v u) / 2 := by
  have hswap : (∑ v, ∑ u, f u * flux G E p v u) =
      -(∑ v, ∑ u, f v * flux G E p v u) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
      rw [flux_swap G E p v u, mul_neg]
  simp only [drift, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum, sub_mul,
    Finset.sum_sub_distrib, hswap]
  ring

/-- Testing the drift against the relative field gives a uniformly
coercive Dirichlet pairing. -/
theorem relativeDirichlet_le_neg_sum_drift (G : WeightedGraph V) (E : V → ℝ) (μ : ℝ)
    (p : V → Occupation) :
    let q := fun v => gibbsOccupation (E v) μ
    let r := relativeField p q
    (Real.exp μ * referenceMargin q ^ 2) * G.dirichlet r r ≤
      -(∑ v, r v * drift G E p v) := by
  let q := fun v => gibbsOccupation (E v) μ
  let r := relativeField p q
  let d := referenceMargin q
  let B (v : V) := relativeWeight (p v) (q v) / (q v : ℝ)
  change (Real.exp μ * d ^ 2) * G.dirichlet r r ≤ -(∑ v, r v * drift G E p v)
  rw [neg_sum_test_mul_drift, WeightedGraph.dirichlet, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun u _ => ?_
  have hJ : flux G E p v u = G.w v u * (Real.exp μ * B v * B u) * (r v - r u) :=
    flux_eq_relativeField G E μ p v u
  have hK : Real.exp μ * d ^ 2 ≤ Real.exp μ * B v * B u := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (relativeWeight_product_ge_margin_sq p q v u) (Real.exp_pos μ).le
  rw [hJ]
  calc
    _ = (G.w v u * (Real.exp μ * d ^ 2)) * ((r v - r u) * (r v - r u)) := by ring
    _ ≤ (G.w v u * (Real.exp μ * B v * B u)) * ((r v - r u) * (r v - r u)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (G.w_nonneg v u)) (mul_self_nonneg _)
    _ = _ := by ring

/-- Equal mass centers the relative field at one half with its particle–hole
weights. Any unweighted center then controls the occupation error. -/
theorem squaredOccupationError_le_relative_variance (p q : V → Occupation)
    (hm : (∑ v, (p v : ℝ)) = ∑ v, (q v : ℝ)) (c : ℝ) :
    (∑ v, ((p v : ℝ) - (q v : ℝ)) ^ 2) ≤ 4 * ∑ v, (relativeField p q v - c) ^ 2 := by
  let r := relativeField p q
  let b (v : V) := relativeWeight (p v) (q v)
  let z (v : V) := r v - 1 / 2
  have he (v : V) : (p v : ℝ) - (q v : ℝ) = 2 * b v * z v := sub_eq_relative_centered _ _
  have hcenter : (∑ v, b v * z v) = 0 := by
    have hzero : (∑ v, ((p v : ℝ) - (q v : ℝ))) = 0 := by
      rw [Finset.sum_sub_distrib, hm, sub_self]
    have hsum : (∑ v, ((p v : ℝ) - (q v : ℝ))) = 2 * ∑ v, b v * z v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => (he v).trans (mul_assoc _ _ _)
    linarith only [hzero, hsum]
  have hvariance : (∑ v, b v * (r v - c) ^ 2) =
      (∑ v, b v * z v ^ 2) + (1 / 2 - c) ^ 2 * ∑ v, b v := by
    have hterm (v : V) : b v * (r v - c) ^ 2 =
        b v * z v ^ 2 + (2 * (1 / 2 - c)) * (b v * z v) + (1 / 2 - c) ^ 2 * b v := by
      dsimp only [z]
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcenter,
      mul_zero, add_zero, ← Finset.mul_sum]
  have hb (v : V) : 0 ≤ b v := (relativeWeight_pos (p v) (q v)).le
  have hb₁ (v : V) : b v ≤ 1 := relativeWeight_le_one (p v) (q v)
  calc
    _ = 4 * ∑ v, b v ^ 2 * z v ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [he v]; ring
    _ ≤ 4 * ∑ v, b v * z v ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right
        (by rw [pow_two]; exact mul_le_of_le_one_right (hb v) (hb₁ v)) (sq_nonneg _)
    _ ≤ 4 * ∑ v, b v * (r v - c) ^ 2 := by
      rw [hvariance]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun v _ => hb v))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun v _ => mul_le_of_le_one_left (sq_nonneg _) (hb₁ v)

/-- The Bernoulli entropy tangent gap is bounded by the chi-square
divergence at every interior comparison and reference. -/
theorem binEntropy_tangent_gap_le_chiSquare (p q : Occupation) :
    Real.binEntropy (q : ℝ) + (Real.log (1 - (q : ℝ)) - Real.log (q : ℝ)) *
      ((p : ℝ) - (q : ℝ)) - Real.binEntropy (p : ℝ) ≤
      ((p : ℝ) - (q : ℝ)) ^ 2 / ((q : ℝ) * (1 - (q : ℝ))) := by
  have h₀ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos p.property.1 q.property.1)) p.property.1.le
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (vacancy_pos p) (vacancy_pos q))) (vacancy_pos p).le
  calc
    _ = (p : ℝ) * Real.log ((p : ℝ) / (q : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))) := by
      rw [Real.log_div p.property.1.ne' q.property.1.ne',
        Real.log_div (vacancy_pos p).ne' (vacancy_pos q).ne']
      simp only [Real.binEntropy, Real.log_inv]
      ring
    _ ≤ (p : ℝ) * ((p : ℝ) / (q : ℝ) - 1) +
        (1 - (p : ℝ)) * ((1 - (p : ℝ)) / (1 - (q : ℝ)) - 1) := add_le_add h₀ h₁
    _ = _ := by
      field_simp [q.property.1.ne', (vacancy_pos q).ne']
      ring

/-- At equal mass, free-energy excess is bounded above by a multiple
of squared occupation error, uniformly over the moving interior field. -/
theorem freeEnergy_gibbs_gap_upper (E : V → ℝ) (μ : ℝ) (p : V → Occupation)
    (hm : (∑ v, (p v : ℝ)) = gibbsMass E μ) :
    let q := fun v => gibbsOccupation (E v) μ
    referenceMargin q ^ 2 *
      (freeEnergy E (fun v => (p v : ℝ)) - freeEnergy E (fun v => (q v : ℝ))) ≤
      ∑ v, ((p v : ℝ) - (q v : ℝ)) ^ 2 := by
  let q := fun v => gibbsOccupation (E v) μ
  let d := referenceMargin q
  let a (v : V) := (E v * (p v : ℝ) - Real.binEntropy (p v : ℝ)) -
    (E v * (q v : ℝ) - Real.binEntropy (q v : ℝ)) -
    chemicalPotential E q v * ((p v : ℝ) - (q v : ℝ))
  have hm' : (∑ v, (p v : ℝ)) = ∑ v, (q v : ℝ) := hm
  have hμ (v : V) : chemicalPotential E q v = μ := chemicalPotential_gibbs E μ v
  have hsum : (∑ v, a v) =
      freeEnergy E (fun v => (p v : ℝ)) - freeEnergy E (fun v => (q v : ℝ)) := by
    simp only [a, freeEnergy, hμ, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hm', sub_self, mul_zero, sub_zero]
  change d ^ 2 * (_ - _) ≤ _
  rw [← hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  let x : ℝ := (p v : ℝ) - (q v : ℝ)
  let s : ℝ := (q v : ℝ) * (1 - (q v : ℝ))
  have hd : 0 < d := referenceMargin_pos q
  have hs : 0 < s := mul_pos (q v).property.1 (vacancy_pos (q v))
  have hds : d ^ 2 ≤ s := by
    rw [pow_two]
    exact mul_le_mul (referenceMargin_le q v).1 (referenceMargin_le q v).2
      hd.le (q v).property.1.le
  have htan : a v ≤ x ^ 2 / s := by
    have h := binEntropy_tangent_gap_le_chiSquare (p v) (q v)
    dsimp only [a, x, s]
    rw [chemicalPotential, Real.log_div (q v).property.1.ne' (vacancy_pos (q v)).ne']
    ring_nf at h ⊢
    linarith only [h]
  change d ^ 2 * a v ≤ x ^ 2
  calc
    _ ≤ d ^ 2 * (x ^ 2 / s) := mul_le_mul_of_nonneg_left htan (sq_nonneg _)
    _ ≤ s * (x ^ 2 / s) := mul_le_mul_of_nonneg_right hds (div_nonneg (sq_nonneg _) hs.le)
    _ = _ := by field_simp [hs.ne']

/-- On a connected graph, all interior fields of a given Gibbs mass obey
a uniform entropy–dissipation inequality. Connectivity supplies the
needed Poincaré constant. -/
theorem exists_dissipation_ge_freeEnergy_gap (G : WeightedGraph V) (E : V → ℝ)
    (μ : ℝ) (root : V) (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v) :
    ∃ k : ℝ, 0 < k ∧ ∀ p : V → Occupation, (∑ v, (p v : ℝ)) = gibbsMass E μ →
      k * (freeEnergy E (fun v => (p v : ℝ)) -
        freeEnergy E (fun v => (gibbsOccupation (E v) μ : ℝ))) ≤ dissipation G E p := by
  let q := fun v => gibbsOccupation (E v) μ
  let d := referenceMargin q
  have hd : 0 < d := referenceMargin_pos q
  obtain ⟨C, hC, hP⟩ := G.exists_anchored_poincare root hpath
  refine ⟨Real.exp μ * d ^ 4 / C, by positivity, fun p hm => ?_⟩
  let r := relativeField p q
  let e := freeEnergy E (fun v => (p v : ℝ)) - freeEnergy E (fun v => (q v : ℝ))
  have hu : d ^ 2 * e ≤ ∑ v, ((p v : ℝ) - (q v : ℝ)) ^ 2 := freeEnergy_gibbs_gap_upper E μ p hm
  have hv : (∑ v, ((p v : ℝ) - (q v : ℝ)) ^ 2) ≤ 4 * ∑ v, (r v - r root) ^ 2 :=
    squaredOccupationError_le_relative_variance p q hm (r root)
  have he : d ^ 2 * e ≤ 4 * (C * G.dirichlet r r) :=
    hu.trans (hv.trans (mul_le_mul_of_nonneg_left (hP r) (by norm_num)))
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ Real.exp μ * d ^ 2 / C by positivity)
  calc
    _ = (Real.exp μ * d ^ 2 / C) * (d ^ 2 * e) := by
      change (Real.exp μ * d ^ 4 / C) * e = _
      ring
    _ ≤ (Real.exp μ * d ^ 2 / C) * (4 * (C * G.dirichlet r r)) := hscaled
    _ = (4 * (Real.exp μ * d ^ 2)) * G.dirichlet r r := by field_simp [hC.ne']
    _ ≤ _ := dissipation_ge_relativeDirichlet G E μ p

/-- The squared drift residual controls squared occupation error at
fixed mass, with a constant uniform over the moving field. -/
theorem exists_drift_residual_bound (G : WeightedGraph V) (E : V → ℝ)
    (μ : ℝ) (root : V) (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v) :
    ∃ L : ℝ, 0 < L ∧ ∀ p : V → Occupation, (∑ v, (p v : ℝ)) = gibbsMass E μ →
      (∑ v, ((p v : ℝ) - (gibbsOccupation (E v) μ : ℝ)) ^ 2) ≤
        L * ∑ v, (drift G E p v) ^ 2 := by
  let q := fun v => gibbsOccupation (E v) μ
  let K := Real.exp μ * referenceMargin q ^ 2
  have hK : 0 < K := mul_pos (Real.exp_pos _) (pow_pos (referenceMargin_pos q) 2)
  obtain ⟨C, hC, hP⟩ := G.exists_anchored_poincare root hpath
  refine ⟨4 * (C ^ 2 / K ^ 2), by positivity, fun p hm => ?_⟩
  let r := relativeField p q
  let f (v : V) := r v - r root
  let g := drift G E p
  let X := ∑ v, f v ^ 2
  let Y := ∑ v, g v ^ 2
  let P := -(∑ v, f v * g v)
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htest : P = -(∑ v, r v * g v) := by
    have hmass : (∑ v, g v) = 0 := sum_drift_eq_zero G E p
    simp only [P, f, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, mul_zero, sub_zero]
  have hD : K * G.dirichlet r r ≤ P := by
    rw [htest]
    exact relativeDirichlet_le_neg_sum_drift G E μ p
  have hp : 0 ≤ P := (mul_nonneg hK.le (G.dirichlet_self_nonneg r)).trans hD
  have hxP : K * X ≤ C * P := by
    calc
      _ ≤ K * (C * G.dirichlet r r) := mul_le_mul_of_nonneg_left (hP r) hK.le
      _ = C * (K * G.dirichlet r r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD hC.le
  have hCS : P ^ 2 ≤ X * Y := by
    dsimp only [P, X, Y]
    rw [neg_sq]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hprod : (K ^ 2 * X) * X ≤ (C ^ 2 * Y) * X := by
    calc
      _ = (K * X) ^ 2 := by ring
      _ ≤ (C * P) ^ 2 := (sq_le_sq₀ (mul_nonneg hK.le hX) (mul_nonneg hC.le hp)).mpr hxP
      _ = C ^ 2 * P ^ 2 := mul_pow _ _ _
      _ ≤ C ^ 2 * (X * Y) := mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = _ := by ring
  have hcancel : K ^ 2 * X ≤ C ^ 2 * Y := by
    rcases hX.eq_or_lt with hz | hz
    · rw [← hz, mul_zero]
      exact mul_nonneg (sq_nonneg _) hY
    · by_contra! hbad
      exact (not_lt_of_ge hprod) (mul_lt_mul_of_pos_right hbad hz)
  have hquot : X ≤ C ^ 2 * Y / K ^ 2 :=
    (le_div_iff₀ (pow_pos hK 2)).mpr (by rw [mul_comm X]; exact hcancel)
  calc
    _ ≤ 4 * X := squaredOccupationError_le_relative_variance p q hm (r root)
    _ ≤ 4 * (C ^ 2 * Y / K ^ 2) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = _ := by change _ = (4 * (C ^ 2 / K ^ 2)) * Y; ring

/-- Each interior mass has a stationary field and a positive dissipation
constant controlling the free-energy gap uniformly on that mass slice. -/
theorem exists_stationary_with_coercive_dissipation (G : WeightedGraph V) (E : V → ℝ)
    (root : V) (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v)
    {m : ℝ} (hm : m ∈ Ioo 0 (Fintype.card V : ℝ)) :
    ∃ q : V → Occupation, (∑ v, (q v : ℝ)) = m ∧ (∀ v, drift G E q v = 0) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ p : V → Occupation, (∑ v, (p v : ℝ)) = m →
        k * (freeEnergy E (fun v => (p v : ℝ)) - freeEnergy E (fun v => (q v : ℝ))) ≤
          dissipation G E p := by
  obtain ⟨μ, hμ, _⟩ := existsUnique_gibbsMass E hm
  obtain ⟨k, hk, hbound⟩ := exists_dissipation_ge_freeEnergy_gap G E μ root hpath
  exact ⟨fun v => gibbsOccupation (E v) μ, hμ, drift_gibbs_eq_zero G E μ,
    k, hk, fun p hp => hbound p (hp.trans hμ.symm)⟩

#print axioms WeightedGraph.exists_anchored_poincare
#print axioms flux_eq_relativeField
#print axioms dissipation_ge_relativeDirichlet
#print axioms relativeDirichlet_le_neg_sum_drift
#print axioms squaredOccupationError_le_relative_variance
#print axioms binEntropy_tangent_gap_le_chiSquare
#print axioms freeEnergy_gibbs_gap_upper
#print axioms exists_dissipation_ge_freeEnergy_gap
#print axioms exists_drift_residual_bound
#print axioms exists_stationary_with_coercive_dissipation

end

end Quantum.FermiGraph

end GaloisForLFunctions.HTGeometry
