import GaloisForLFunctions.HTGeometry.TwoTermBlowUpNoGo

/-!
# Independence of a monomial box transports along an invertible change of basis

Blow-up data is local and cannot see a constant.  A change of basis is global and sees nothing else:
it recombines the monomials of a box without touching the degree factor, so it preserves independence
exactly.

That is the missing half.  A box whose rates collide is decided as soon as *some* invertible
recombination of its monomials has separated rates — and the constant that defeats every finite-order
local invariant is precisely such a recombination.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## The transport law -/

/-- **Independence transports along an invertible recombination of the first index.**  The
recombination acts on the monomials and leaves the degree index alone. -/
theorem linearIndependent_of_blockComb {κ ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Fintype κ] [DecidableEq κ] [Fintype ι] {v w : κ × ι → M} {T : Matrix κ κ K}
    (hT : IsUnit T.det)
    (hcomb : ∀ a i, v (a, i) = ∑ b, T a b • w (b, i))
    (h : LinearIndependent K w) : LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc
  set g : κ × ι → K := fun p => ∑ a, c (a, p.2) * T a p.1 with hg
  have hzero : ∑ p : κ × ι, g p • w p = 0 := by
    rw [Fintype.sum_prod_type]
    calc ∑ b, ∑ i, g (b, i) • w (b, i)
        = ∑ b, ∑ i, ∑ a, (c (a, i) * T a b) • w (b, i) := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hg, Finset.sum_smul]
      _ = ∑ b, ∑ a, ∑ i, (c (a, i) * T a b) • w (b, i) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, (c (a, i) * T a b) • w (b, i) := Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, (c (a, i) * T a b) • w (b, i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ i, c (a, i) • v (a, i) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hcomb a i, Finset.smul_sum]
          exact (Finset.sum_congr rfl fun b _ => by rw [smul_smul]).symm
      _ = ∑ p : κ × ι, c p • v p :=
          (Fintype.sum_prod_type (fun p : κ × ι => c p • v p)).symm
      _ = 0 := hc
  have hvec : ∀ i : ι, Matrix.vecMul (fun a => c (a, i)) T = 0 := by
    intro i
    funext b
    exact h g hzero (b, i)
  intro p
  have hback : (fun a => c (a, p.2)) = 0 := by
    have hmul := congrArg (fun x => Matrix.vecMul x T⁻¹) (hvec p.2)
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hT] using hmul
  exact congrFun hback p.1

/-! ## A separating recombination decides the box -/

/-- **The search is a theorem.**  A box whose monomials are an invertible recombination of a family
with distinct blow-up orders is independent.  This is the exact complement of the finite-order no-go:
local data cannot see a constant, and a recombination sees nothing else. -/
theorem linearIndependent_of_separatingRecombination {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q : ℕ} {S Z : Set ℂ} {M M' : κ → ℂ → ℂ} {ord : κ → ℕ} {T : Matrix κ κ ℂ}
    (hT : IsUnit T.det) (hcomb : ∀ a w, M a w = ∑ b, T a b * M' b w)
    (hdata : GradedBlowUpFamily S M' Z ord) (hord : Function.Injective ord) :
    LinearIndependent ℂ
      (fun p : κ × Fin (q + 1) => Set.restrict S (fun w => w ^ (p.2 : ℕ) * M p.1 w)) := by
  refine linearIndependent_of_blockComb hT ?_
    (linearIndependent_restrict_degreeBox_of_gradedBlowUp hdata hord)
  intro a i
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.restrict_apply]
  rw [hcomb a (x : ℂ), Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ## Constant shifts are invertible recombinations -/

/-- The reference box: the constant monomial and the jet. -/
noncomputable def unitJetExponent : Fin 2 → (Fin 1 →₀ ℕ) := ![0, Finsupp.single 0 1]

/-- The shifted box: the jet and the jet plus one. -/
noncomputable def shiftedJetPair (G : ℂ → ℂ) : Fin 2 → ℂ → ℂ := ![G, fun w => G w + 1]

theorem expandedMonomialFamily_unitJetExponent (G : ℂ → ℂ) (q : ℕ) (a : Fin 2) (i : Fin (q + 1))
    (w : ℂ) :
    expandedMonomialFamily ![G] unitJetExponent q (a, i) w
      = w ^ (i : ℕ) * (if a = 0 then 1 else G w) := by
  rw [expandedMonomialFamily_apply]
  fin_cases a
  · simp [unitJetExponent]
  · simp [unitJetExponent, Finsupp.support_single]

theorem expandedMonomialFamily_shiftedJetPair (G : ℂ → ℂ) (q : ℕ) (a : Fin 2) (i : Fin (q + 1))
    (w : ℂ) :
    expandedMonomialFamily (shiftedJetPair G) boxExponent q (a, i) w
      = w ^ (i : ℕ) * (if a = 0 then G w else G w + 1) := by
  rw [expandedMonomialFamily_apply]
  fin_cases a
  · simp [boxExponent, shiftedJetPair, Finsupp.support_single]
  · simp [boxExponent, shiftedJetPair, Finsupp.support_single]


/-- **A constant shift is an invertible recombination.**  If the box `{1, G}` is independent on a
region, so is the box `{G, G + 1}` — for every degree budget. -/
theorem linearIndependent_restrict_shiftedJetPair {S : Set ℂ} {G : ℂ → ℂ} {q : ℕ}
    (h : LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict S (expandedMonomialFamily ![G] unitJetExponent q p))) :
    LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict S (expandedMonomialFamily (shiftedJetPair G) boxExponent q p)) := by
  refine linearIndependent_of_blockComb (T := !![(0 : ℂ), 1; 1, 1]) ?_ ?_ h
  · rw [Matrix.det_fin_two_of]
    norm_num
  · intro a i
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.restrict_apply,
      Fin.sum_univ_two]
    rw [expandedMonomialFamily_shiftedJetPair, expandedMonomialFamily_unitJetExponent,
      expandedMonomialFamily_unitJetExponent]
    fin_cases a <;> (simp; try ring)

/-! ## The colliding pair, decided -/

theorem blowUpOrder_zero {n : ℕ} (d : Fin n → ℕ) : blowUpOrder d 0 = 0 := by
  rw [blowUpOrder]
  simp

theorem blowUpOrder_single {n : ℕ} (d : Fin n → ℕ) (k : Fin n) (m : ℕ) :
    blowUpOrder d (Finsupp.single k m) = m * d k := by
  rw [blowUpOrder, Finsupp.sum_single_index]
  simp

/-- The reference box of the pole square has separated rates, hence is independent. -/
theorem linearIndependent_restrict_poleSquare_unitBox (q : ℕ) :
    LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict upperHalfPlane
        (expandedMonomialFamily ![poleSquare] unitJetExponent q p)) := by
  have hF : (fun (k : Fin 1) (w : ℂ) => periodicPoleModel w ^ ((![2] : Fin 1 → ℕ) k))
      = ![poleSquare] := by
    funext k w
    fin_cases k
    rfl
  have hdata := multiBlowUpData_periodicPolePowers (![2] : Fin 1 → ℕ)
  rw [hF] at hdata
  refine linearIndependent_restrict_expandedMonomialFamily_of_multiBlowUp hdata ?_
  intro a b hab
  have hval : ∀ c : Fin 2, blowUpOrder (![2] : Fin 1 → ℕ) (unitJetExponent c)
      = if c = 0 then 0 else 2 := by
    intro c
    fin_cases c
    · simp [unitJetExponent, blowUpOrder_zero]
    · simp [unitJetExponent, blowUpOrder_single]
  simp only [hval] at hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- **The colliding pair is independent for every degree budget.**  Its rates collide, so no
blow-up criterion can apply; the constant that hides from every local invariant is exactly the
invertible recombination that separates the rates. -/
theorem linearIndependent_restrict_collidingPairShifted (q : ℕ) :
    LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict upperHalfPlane
        (expandedMonomialFamily collidingPairShifted boxExponent q p)) :=
  linearIndependent_restrict_shiftedJetPair (linearIndependent_restrict_poleSquare_unitBox q)


/-! ## The elimination step -/

/-- **Leading-coefficient elimination.**  Two members of equal blow-up order admit a combination
whose leading value cancels: the leading-value map is linear with one-dimensional image, so colliding
members can always be recombined to lower the order. -/
theorem tendsto_leadingElimination {f g : ℂ → ℂ} {u t : ℕ → ℂ} {m : ℕ} {α β : ℂ}
    (hf : Tendsto (fun j => f (u j) * t j ^ m) atTop (𝓝 α))
    (hg : Tendsto (fun j => g (u j) * t j ^ m) atTop (𝓝 β)) :
    Tendsto (fun j => (β * f (u j) - α * g (u j)) * t j ^ m) atTop (𝓝 0) := by
  have h := (hf.const_mul β).sub (hg.const_mul α)
  have hz : β * α - α * β = 0 := by ring
  rw [hz] at h
  refine h.congr fun j => ?_
  ring

/-- **The elimination step decides a colliding pair.**  Replacing the second member by the
leading-coefficient elimination is an invertible recombination, so distinct orders for the
replacement decide the original box. -/
theorem linearIndependent_of_eliminationStep {q : ℕ} {S Z : Set ℂ} {f g : ℂ → ℂ}
    {α β : ℂ} (hα : α ≠ 0) {ord : Fin 2 → ℕ}
    (hdata : GradedBlowUpFamily S ![f, fun w => β * f w - α * g w] Z ord)
    (hord : Function.Injective ord) :
    LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict S (fun w => w ^ (p.2 : ℕ) * (![f, g] p.1) w)) := by
  refine linearIndependent_of_separatingRecombination
    (T := !![1, 0; β / α, -(1 / α)]) ?_ ?_ hdata hord
  · rw [Matrix.det_fin_two_of]
    have hne : -(1 / α) ≠ 0 := by
      simp [hα]
    simpa using isUnit_iff_ne_zero.mpr hne
  · intro a w
    fin_cases a
    · simp
    · show g w = ∑ b, (!![(1 : ℂ), 0; β / α, -(1 / α)]) 1 b *
        (![f, fun w => β * f w - α * g w] b) w
      rw [Fin.sum_univ_two]
      have h10 : (!![(1 : ℂ), 0; β / α, -(1 / α)]) 1 0 = β / α := rfl
      have h11 : (!![(1 : ℂ), 0; β / α, -(1 / α)]) 1 1 = -(1 / α) := rfl
      have hf0 : (![f, fun w => β * f w - α * g w] : Fin 2 → ℂ → ℂ) 0 = f := rfl
      have hf1 : (![f, fun w => β * f w - α * g w] : Fin 2 → ℂ → ℂ) 1
          = fun w => β * f w - α * g w := rfl
      rw [h10, h11, hf0, hf1]
      field_simp
      ring

end GaloisForLFunctions.HTGeometry
