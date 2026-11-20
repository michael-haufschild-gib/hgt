import GaloisForLFunctions.HTGeometry.WeightedGraphSpectralGap
import GaloisForLFunctions.HilbertMetric.QuantumInformation.FermionSpectralEntropy
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp

/-!
# Pauli-blocked transport and free energy on a finite graph

For occupations in (0,1), the graph current is the difference of two
particle-hole fluxes. Its contribution to free-energy dissipation is
nonnegative on each edge, the finite analogue of the chemical-potential
dissipation in Hyun (arXiv:2611.22558, Section 2.3).
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

noncomputable section

variable {V : Type*} [Fintype V]

/-- A mode occupation in the interior of the Pauli interval. -/
abbrev Occupation := Set.Ioo (0 : ℝ) 1

/-- The derivative of energy minus binary entropy at an occupied site. -/
def chemicalPotential (E : V → ℝ) (p : V → Occupation) (v : V) : ℝ :=
  E v + Real.log ((p v : ℝ) / (1 - (p v : ℝ)))

/-- Free energy of the diagonal correlation spectrum, in temperature units. -/
def freeEnergy (E x : V → ℝ) : ℝ := ∑ v, (E v * x v - Real.binEntropy (x v))

omit [Fintype V] in
private theorem vacancy_pos (p : V → Occupation) (v : V) : 0 < 1 - (p v : ℝ) :=
  sub_pos.mpr (p v).2.2

/-- The entropy in the graph free energy is the corpus's fermion spectral entropy. -/
theorem freeEnergy_eq_spectral [DecidableEq V] (E x : V → ℝ) :
    freeEnergy E x = (∑ v, E v * x v) -
      HilbertMetric.fermionSpectralEntropy (Matrix.diagonal fun v => (x v : ℂ)) := by
  rw [HilbertMetric.fermionSpectralEntropy_diagonal, freeEnergy, Finset.sum_sub_distrib]

/-- The net outward current, factored into vacancies and activity difference. -/
def flux (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) (v u : V) : ℝ :=
  G.w v u * ((1 - (p v : ℝ)) * (1 - (p u : ℝ))) *
    (Real.exp (chemicalPotential E p v) - Real.exp (chemicalPotential E p u))

omit [Fintype V] in
/-- Each forward jump carries the departure occupation and arrival vacancy. -/
theorem flux_eq_particle_hole (G : WeightedGraph V) (E : V → ℝ)
    (p : V → Occupation) (v u : V) :
    flux G E p v u = G.w v u *
      (Real.exp (E v) * (p v : ℝ) * (1 - (p u : ℝ)) -
        Real.exp (E u) * (p u : ℝ) * (1 - (p v : ℝ))) := by
  have he (k : V) : Real.exp (chemicalPotential E p k) =
      Real.exp (E k) * ((p k : ℝ) / (1 - (p k : ℝ))) := by
    rw [chemicalPotential, Real.exp_add, Real.exp_log
      (div_pos (p k).2.1 (vacancy_pos p k))]
  rw [flux, he v, he u]
  field_simp [(vacancy_pos p v).ne', (vacancy_pos p u).ne']

omit [Fintype V] in
theorem flux_swap (G : WeightedGraph V) (E : V → ℝ)
    (p : V → Occupation) (v u : V) :
    flux G E p u v = -flux G E p v u := by
  simp only [flux, G.w_symm u v]
  ring

/-- Local time derivative from conservation of particle current. -/
def drift (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) (v : V) : ℝ :=
  -∑ u, flux G E p v u

/-- The sum of occupations has zero rate of change. -/
theorem sum_drift_eq_zero (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    ∑ v, drift G E p v = 0 := by
  have h : (∑ v, ∑ u, flux G E p v u) = -(∑ v, ∑ u, flux G E p v u) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => flux_swap G E p v u
  simp only [drift, Finset.sum_neg_distrib]
  linarith only [h]

/-- Dissipated free energy is the current times the chemical potential drop,
with each unoriented edge counted once. -/
def dissipation (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) : ℝ :=
  (∑ v, ∑ u, (chemicalPotential E p v - chemicalPotential E p u) * flux G E p v u) / 2

omit [Fintype V] in
private theorem edge_nonneg (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) (v u : V) :
    0 ≤ (chemicalPotential E p v - chemicalPotential E p u) * flux G E p v u := by
  rw [flux, ← mul_left_comm]
  apply mul_nonneg
    (mul_nonneg (G.w_nonneg v u) (mul_nonneg (vacancy_pos p v).le (vacancy_pos p u).le))
  rcases le_total (chemicalPotential E p v) (chemicalPotential E p u) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.exp_le_exp.mpr h))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.exp_le_exp.mpr h))

theorem dissipation_nonneg (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    0 ≤ dissipation G E p :=
  div_nonneg (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ =>
    edge_nonneg G E p v u) (by positivity)

/-- Zero production is equivalent to chemical-potential balance on each positive edge. -/
theorem dissipation_eq_zero_iff (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    dissipation G E p = 0 ↔
      ∀ v u, 0 < G.w v u → chemicalPotential E p v = chemicalPotential E p u := by
  rw [dissipation, div_eq_zero_iff, or_iff_left (two_ne_zero : (2 : ℝ) ≠ 0)]
  constructor
  · intro h v u hw
    have hv := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun b _ => edge_nonneg G E p a b)).mp h v
      (Finset.mem_univ v)
    have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => edge_nonneg G E p v b)).mp hv u
      (Finset.mem_univ u)
    rcases mul_eq_zero.mp hu with hμ | hJ
    · exact sub_eq_zero.mp hμ
    · rw [flux] at hJ
      exact Real.exp_injective (sub_eq_zero.mp ((mul_eq_zero.mp hJ).resolve_left
        (mul_pos hw (mul_pos (vacancy_pos p v) (vacancy_pos p u))).ne'))
  · intro h
    refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun u _ => ?_
    rcases (G.w_nonneg v u).eq_or_lt with hw | hw
    · simp only [flux, ← hw, zero_mul, mul_zero]
    · rw [h v u hw, sub_self, zero_mul]

/-- Graph integration by parts pairs the transport velocity with the free
energy gradient. -/
theorem sum_chemicalPotential_mul_drift (G : WeightedGraph V) (E : V → ℝ)
    (p : V → Occupation) :
    (∑ v, chemicalPotential E p v * drift G E p v) = -dissipation G E p := by
  have hswap : (∑ v, ∑ u, chemicalPotential E p u * flux G E p v u) =
      -(∑ v, ∑ u, chemicalPotential E p v * flux G E p v u) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
      rw [flux_swap G E p v u, mul_neg]
  simp only [dissipation, sub_mul, Finset.sum_sub_distrib, hswap, drift, mul_neg,
    Finset.mul_sum, Finset.sum_neg_distrib]
  ring

/-- A stationary field has detailed balance on all occupied edges, and every
field with detailed balance is stationary. -/
theorem drift_eq_zero_iff (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    (∀ v, drift G E p v = 0) ↔
      ∀ v u, 0 < G.w v u → chemicalPotential E p v = chemicalPotential E p u := by
  constructor
  · intro h
    have h' := sum_chemicalPotential_mul_drift G E p
    simp only [h, mul_zero, Finset.sum_const_zero] at h'
    exact (dissipation_eq_zero_iff G E p).mp (by linarith only [h'])
  · intro h v
    unfold drift
    suffices (∑ u, flux G E p v u) = 0 by rw [this, neg_zero]
    refine Finset.sum_eq_zero fun u _ => ?_
    rcases (G.w_nonneg v u).eq_or_lt with hw | hw
    · simp only [flux, ← hw, zero_mul]
    · simp only [flux, h v u hw, sub_self, mul_zero]

/-- The actual derivative along the graph transport direction equals the
negative dissipation at every interior occupation field. -/
theorem hasDerivAt_freeEnergy_drift (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    HasDerivAt (fun t : ℝ => freeEnergy E (fun v => (p v : ℝ) + t * drift G E p v))
      (-dissipation G E p) 0 := by
  rw [← sum_chemicalPotential_mul_drift]
  unfold freeEnergy
  apply HasDerivAt.fun_sum
  intro v _
  let q := (p v : ℝ)
  let d := drift G E p v
  have hq : HasDerivAt (fun t : ℝ => q + t * d) d 0 := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id (0 : ℝ)).mul_const d).const_add q)
  have hb : HasDerivAt (fun t : ℝ => Real.binEntropy (q + t * d))
      ((Real.log (1 - q) - Real.log q) * d) 0 := by
    have hbin : HasDerivAt Real.binEntropy (Real.log (1 - q) - Real.log q)
        ((fun t : ℝ => q + t * d) 0) := by
      simpa only [zero_mul, add_zero] using
        (Real.hasDerivAt_binEntropy (p v).2.1.ne' (p v).2.2.ne)
    change HasDerivAt (Real.binEntropy ∘ fun t : ℝ => q + t * d) _ 0
    exact hbin.comp 0 hq
  have he : E v * d - (Real.log (1 - q) - Real.log q) * d =
      chemicalPotential E p v * d := by
    rw [chemicalPotential, Real.log_div (p v).2.1.ne' (vacancy_pos p v).ne']
    change _ = (E v + (Real.log q - Real.log (1 - q))) * d
    ring
  have hres := (hq.const_mul (E v)).sub hb
  rw [he] at hres
  change HasDerivAt
    ((fun t : ℝ => E v * (q + t * d)) - (fun t : ℝ => Real.binEntropy (q + t * d)))
    (chemicalPotential E p v * d) 0
  exact hres

/-- Fermi--Dirac occupation at the indicated energy and chemical potential. -/
def gibbsOccupation (e μ : ℝ) : Occupation :=
  ⟨1 / (1 + Real.exp (e - μ)), by
    have h : 0 < Real.exp (e - μ) := Real.exp_pos _
    have hd : 0 < 1 + Real.exp (e - μ) := by positivity
    exact ⟨div_pos one_pos hd, (div_lt_iff₀ hd).mpr (by linarith only [h])⟩⟩

omit [Fintype V] in
/-- The Fermi--Dirac profile has exactly the prescribed chemical potential. -/
theorem chemicalPotential_gibbs (E : V → ℝ) (μ : ℝ) (v : V) :
    chemicalPotential E (fun u => gibbsOccupation (E u) μ) v = μ := by
  let z := Real.exp (E v - μ)
  have hz : 0 < z := Real.exp_pos _
  have hd : 0 < 1 + z := by positivity
  have hratio : (1 / (1 + z)) / (1 - 1 / (1 + z)) = z⁻¹ := by
    have hv : 1 - 1 / (1 + z) = z / (1 + z) := by
      field_simp [hd.ne']
      ring
    rw [hv]
    field_simp [hd.ne', hz.ne']
  change E v + Real.log ((1 / (1 + z)) / (1 - 1 / (1 + z))) = μ
  rw [hratio, Real.log_inv]
  change E v + -Real.log (Real.exp (E v - μ)) = μ
  rw [Real.log_exp]
  ring

omit [Fintype V] in
/-- The chemical potential is an exact coordinate on interior occupations. -/
theorem chemicalPotential_eq_iff (E : V → ℝ) (p : V → Occupation) (μ : ℝ) (v : V) :
    chemicalPotential E p v = μ ↔ p v = gibbsOccupation (E v) μ := by
  constructor
  · intro h
    let q : V → Occupation := fun u => gibbsOccupation (E u) μ
    have hc : chemicalPotential E p v = chemicalPotential E q v :=
      h.trans (chemicalPotential_gibbs E μ v).symm
    have hl : Real.log ((p v : ℝ) / (1 - (p v : ℝ))) =
        Real.log ((q v : ℝ) / (1 - (q v : ℝ))) :=
      add_left_cancel hc
    have hr := congrArg Real.exp hl
    rw [Real.exp_log (div_pos (p v).2.1 (vacancy_pos p v)),
      Real.exp_log (div_pos (q v).2.1 (vacancy_pos q v))] at hr
    apply Subtype.ext
    change (p v : ℝ) = (q v : ℝ)
    have hm := (div_eq_div_iff (vacancy_pos p v).ne' (vacancy_pos q v).ne').mp hr
    linarith only [show (p v : ℝ) * (1 - (q v : ℝ)) =
      (q v : ℝ) * (1 - (p v : ℝ)) from hm]
  · intro h
    unfold chemicalPotential
    rw [h]
    exact chemicalPotential_gibbs E μ v

/-- Every Fermi--Dirac profile with a common chemical potential is stationary. -/
theorem drift_gibbs_eq_zero (G : WeightedGraph V) (E : V → ℝ) (μ : ℝ) :
    ∀ v, drift G E (fun u => gibbsOccupation (E u) μ) v = 0 := by
  apply (drift_eq_zero_iff _ _ _).mpr
  intro v u _
  rw [chemicalPotential_gibbs, chemicalPotential_gibbs]

/-- On a connected graph, the Gibbs profiles exhaust the stationary fields. -/
theorem stationary_iff_gibbs_of_paths (G : WeightedGraph V) (E : V → ℝ)
    (p : V → Occupation) (v₀ : V) :
    (∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) v₀ v) →
      ((∀ v, drift G E p v = 0) ↔ ∃ μ, p = fun u => gibbsOccupation (E u) μ) := by
  intro hpath
  constructor
  · intro h
    have he := (drift_eq_zero_iff G E p).mp h
    refine ⟨chemicalPotential E p v₀, funext fun v => ?_⟩
    apply (chemicalPotential_eq_iff E p (chemicalPotential E p v₀) v).mp
    induction hpath v with
    | refl => rfl
    | tail _ edge ih => exact (he _ _ edge).symm.trans ih
  · rintro ⟨μ, rfl⟩
    exact drift_gibbs_eq_zero G E μ

#print axioms flux_eq_particle_hole
#print axioms freeEnergy_eq_spectral
#print axioms sum_drift_eq_zero
#print axioms dissipation_eq_zero_iff
#print axioms drift_eq_zero_iff
#print axioms hasDerivAt_freeEnergy_drift
#print axioms chemicalPotential_eq_iff
#print axioms stationary_iff_gibbs_of_paths

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
