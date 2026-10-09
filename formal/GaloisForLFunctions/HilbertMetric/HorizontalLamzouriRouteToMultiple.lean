import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriFailureCount

/-!
# Routing nearly real pairs to the multiple real points

A conjugate pair `q` enters the packet as the two atoms `(2m_q, g_q)` and `(−2m_q, h_q)`. If the
odd vector `h_q` is small, the pair behaves like a real point of multiplicity `2m_q` with vector
`g_q`. For a set `S` of pairs, `routeToMultiple S` keeps `(2m_q, g_q)` as a multiple real point
for `q ∈ S` and drops `h_q`; the count is unchanged.

**Exact routing identity** (`four_mass_sub_energy_route_eq`). Let `D′` be the diagonal form of the
routed packet. Then
`4·mass − E − 2N = 4·mass′ − E′ − 2N′ − Σ_{q∈S} 2m_q(4‖h_q‖² − 2D′(h_q))
  − Σ_{q,q′∈S} 4m_q m_{q′}⟪h_q, h_{q′}⟫²`.
This is the expansion of `X ↦ 4 tr X − ‖X‖²` at `X = K′ − H`, where `H = Σ_S 2m_q h_q⊗h_q`.

**Routing bound** (`four_mass_sub_energy_le_route`). Routing costs at most
`Σ_{q∈S} 4m_q(D′(h_q) − 2‖h_q‖²)`. Each term is at most `4m_q‖h_q‖²(⟪K′ĥ_q, ĥ_q⟫ − 2)`; it is small
when `h_q` is small, and is nonpositive when the routed kernel sees less than `2` in the direction
`ĥ_q`.

**Routed failure count** (`four_mass_sub_energy_le_route_add_card_fail`). Combined with the budget
count on the routed packet:
`4·mass − E − 2N ≤ #H + #{uncertified mixed points of the routed packet}
  + Σ_{q∈S} 4m_q(D′(h_q) − 2‖h_q‖²)`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
  [DecidableEq ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP) (S : Finset ιP)

/-- The packet in which the pairs of `S` become multiple real points `(2m_q, g_q)`. -/
def routeToMultiple : HorizontalPacket V (ι₂ ⊕ {q // q ∈ S}) ιH ιM {q // q ∉ S} where
  f₂ := Sum.elim P.f₂ fun q => P.g q
  m₂ := Sum.elim P.m₂ fun q => 2 * P.mP q
  fH := P.fH
  fM := P.fM
  g q := P.g q
  h q := P.h q
  mP q := P.mP q

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] in
theorem sum_mem_add_sum_not_mem (F : ιP → ℝ) :
    ∑ q : {q // q ∈ S}, F q + ∑ q : {q // q ∉ S}, F q = ∑ q, F q := by
  convert Fintype.sum_subtype_add_sum_subtype (fun q => q ∈ S) F

/-- Weighted sums over the routed packet gain the dropped odd atoms. -/
theorem route_sum_wt_mul (F : V → ℝ) :
    ∑ k, (P.routeToMultiple S).wt k * F ((P.routeToMultiple S).vec k) =
      ∑ k, P.wt k * F (P.vec k) + ∑ q : {q // q ∈ S}, 2 * P.mP q * F (P.h q) := by
  rw [sum_wt_mul, sum_wt_mul]
  have hg := sum_mem_add_sum_not_mem S fun q => 2 * P.mP q * F (P.g q)
  have hh := sum_mem_add_sum_not_mem S fun q => 2 * P.mP q * F (P.h q)
  simp only [routeToMultiple, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [← hg, ← hh]
  ring

theorem route_mass :
    (P.routeToMultiple S).mass = P.mass + ∑ q : {q // q ∈ S}, 2 * P.mP q * ‖P.h q‖ ^ 2 :=
  P.route_sum_wt_mul S fun v => ‖v‖ ^ 2

theorem route_diagForm (ψ : V) :
    (P.routeToMultiple S).diagForm ψ =
      P.diagForm ψ + ∑ q : {q // q ∈ S}, 2 * P.mP q * ⟪P.h q, ψ⟫ ^ 2 :=
  P.route_sum_wt_mul S fun v => ⟪v, ψ⟫ ^ 2

theorem route_count : (P.routeToMultiple S).count = P.count := by
  simp only [count, routeToMultiple, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have := sum_mem_add_sum_not_mem S P.mP
  have e : ∑ q : {q // q ∈ S}, 2 * P.mP q = 2 * ∑ q : {q // q ∈ S}, P.mP q := by
    rw [Finset.mul_sum]
  rw [e, ← this]
  ring

theorem route_energy :
    (P.routeToMultiple S).energy = P.energy +
      2 * ∑ q : {q // q ∈ S}, 2 * P.mP q * (P.routeToMultiple S).diagForm (P.h q) -
      ∑ q : {q // q ∈ S}, ∑ q' : {q // q ∈ S},
        2 * P.mP q * (2 * P.mP q') * ⟪P.h q, P.h q'⟫ ^ 2 := by
  set D' := (P.routeToMultiple S).diagForm with hD'
  rw [energy_eq_sum_diagForm, P.route_sum_wt_mul S D']
  have h1 : ∑ k, P.wt k * D' (P.vec k) = P.energy +
      ∑ q : {q // q ∈ S}, 2 * P.mP q * P.diagForm (P.h q) := by
    simp only [hD', route_diagForm, mul_add, Finset.sum_add_distrib, ← energy_eq_sum_diagForm]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [diagForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm]; ring
  have h2 : ∀ q : {q // q ∈ S}, P.diagForm (P.h q) =
      D' (P.h q) - ∑ q' : {q // q ∈ S}, 2 * P.mP q' * ⟪P.h q', P.h q⟫ ^ 2 := fun q => by
    rw [hD', route_diagForm]; ring
  have h4 : ∑ q : {q // q ∈ S}, 2 * P.mP q * P.diagForm (P.h q) =
      ∑ q : {q // q ∈ S}, 2 * P.mP q * D' (P.h q) - ∑ q : {q // q ∈ S}, ∑ q' : {q // q ∈ S},
        2 * P.mP q * (2 * P.mP q') * ⟪P.h q, P.h q'⟫ ^ 2 := by
    simp only [h2, mul_sub, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [real_inner_comm]; ring
  rw [h1, h4]
  ring

/-- **Exact routing identity.** -/
theorem four_mass_sub_energy_route_eq :
    4 * P.mass - P.energy - 2 * P.count =
      4 * (P.routeToMultiple S).mass - (P.routeToMultiple S).energy -
          2 * (P.routeToMultiple S).count -
        ∑ q : {q // q ∈ S}, 2 * P.mP q *
          (4 * ‖P.h q‖ ^ 2 - 2 * (P.routeToMultiple S).diagForm (P.h q)) -
        ∑ q : {q // q ∈ S}, ∑ q' : {q // q ∈ S},
          2 * P.mP q * (2 * P.mP q') * ⟪P.h q, P.h q'⟫ ^ 2 := by
  rw [route_mass, route_energy, route_count]
  have e : ∑ q : {q // q ∈ S}, 2 * P.mP q *
      (4 * ‖P.h q‖ ^ 2 - 2 * (P.routeToMultiple S).diagForm (P.h q)) =
      4 * ∑ q : {q // q ∈ S}, 2 * P.mP q * ‖P.h q‖ ^ 2 -
        2 * ∑ q : {q // q ∈ S}, 2 * P.mP q * (P.routeToMultiple S).diagForm (P.h q) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e]
  ring

/-- **Routing bound.** -/
theorem four_mass_sub_energy_le_route (hmP : ∀ q, 1 ≤ P.mP q) :
    4 * P.mass - P.energy - 2 * P.count ≤
      4 * (P.routeToMultiple S).mass - (P.routeToMultiple S).energy -
          2 * (P.routeToMultiple S).count +
        ∑ q : {q // q ∈ S}, 4 * P.mP q *
          ((P.routeToMultiple S).diagForm (P.h q) - 2 * ‖P.h q‖ ^ 2) := by
  rw [P.four_mass_sub_energy_route_eq S]
  have hpos : 0 ≤ ∑ q : {q // q ∈ S}, ∑ q' : {q // q ∈ S},
      2 * P.mP q * (2 * P.mP q') * ⟪P.h q, P.h q'⟫ ^ 2 :=
    Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun q' _ =>
      mul_nonneg (mul_nonneg (by linarith [hmP q]) (by linarith [hmP q'])) (sq_nonneg _)
  have heq : ∑ q : {q // q ∈ S}, 4 * P.mP q *
      ((P.routeToMultiple S).diagForm (P.h q) - 2 * ‖P.h q‖ ^ 2) =
      -∑ q : {q // q ∈ S}, 2 * P.mP q *
        (4 * ‖P.h q‖ ^ 2 - 2 * (P.routeToMultiple S).diagForm (P.h q)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [heq]
  linarith

/-- **Routed failure count.** -/
theorem four_mass_sub_energy_le_route_add_card_fail [FiniteDimensional ℝ V] [DecidableEq ιM]
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hMn : ∀ x, ‖P.fM x‖ ≤ 1) (own : ιM → {q // q ∉ S}) (O : Finset {q // q ∉ S})
    (hO : ∀ x, own x ∈ O) (hOne : O.Nonempty) (β : {q // q ∉ S} → ℝ)
    (hβ0 : ∀ q ∈ O, 0 ≤ β q) (hβ1 : ∑ q ∈ O, β q ≤ 1) (good : Finset ιM)
    (hgood : ∀ x ∈ good, (P.routeToMultiple S).CertifiedWith own β x) :
    4 * P.mass - P.energy - 2 * P.count ≤
      (Fintype.card ιH : ℝ) + (Finset.univ \ good).card +
        ∑ q : {q // q ∈ S}, 4 * P.mP q *
          ((P.routeToMultiple S).diagForm (P.h q) - 2 * ‖P.h q‖ ^ 2) := by
  have hm₂' : ∀ i, 2 ≤ (P.routeToMultiple S).m₂ i := by
    rintro (i | q)
    · exact hm₂ i
    · show 2 ≤ 2 * P.mP q; linarith [hmP q]
  have h := (P.routeToMultiple S).four_mass_sub_energy_le_add_card_fail_budget hm₂'
    (fun q => hmP q) hH hMn own O hO hOne β hβ0 hβ1 good hgood
  have := P.four_mass_sub_energy_le_route S hmP
  linarith

end HorizontalPacket

end GaloisForLFunctions.HilbertMetric
