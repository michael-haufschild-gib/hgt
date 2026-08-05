import GaloisForLFunctions.HTGeometry.MultiJetBlowUpIndependence
import GaloisForLFunctions.HTGeometry.PoleJetAlgebraicIndependence

/-!
# Orders may be negative

A member of a family need not blow up at a sampled point: it may vanish there.  The graded law only
admits blow-up, so a vanishing member has no order in it and the family falls outside its reach.

Nothing in the argument needs the orders to be non-negative.  The relation is multiplied by
`t ^ (D − ord a)`, a difference of the maximal order with the member's own, which is non-negative
however the individual orders sit.  Allowing integer orders therefore costs only the requirement that
the scale be nonzero, and it makes vanishing a datum rather than an obstruction: a member vanishing
to order `v` simply has order `−v`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A family with prescribed **integer** orders and nonzero leading values: positive orders are
blow-up, negative orders are vanishing. -/
def IntegerGradedFamily {κ : Type*} (S : Set ℂ) (M : κ → ℂ → ℂ) (Z : Set ℂ) (ord : κ → ℤ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (C : κ → ℂ),
    (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ a, C a ≠ 0) ∧ ∀ a, Tendsto (fun j => M a (u j) * t j ^ (ord a)) atTop (𝓝 (C a))

set_option maxHeartbeats 1000000 in
/-- **Distinct integer orders make a degree box independent.**  Members that vanish at the sampled
points are handled on the same footing as members that blow up. -/
theorem linearIndependent_restrict_degreeBox_of_integerGraded
    {κ : Type*} [Fintype κ] [DecidableEq κ] {q : ℕ} {S : Set ℂ} {M : κ → ℂ → ℂ}
    {Z : Set ℂ} {ord : κ → ℤ} (hdata : IntegerGradedFamily S M Z ord)
    (hord : Function.Injective ord) :
    LinearIndependent ℂ
      (fun p : κ × Fin (q + 1) => Set.restrict S (fun w => w ^ (p.2 : ℕ) * M p.1 w)) := by
  classical
  obtain ⟨hZ, hblow⟩ := hdata
  rw [Fintype.linearIndependent_iff]
  intro lam hlam
  have hrel : ∀ w ∈ S, ∑ c : κ × Fin (q + 1), lam c * (w ^ (c.2 : ℕ) * M c.1 w) = 0 := by
    intro w hw
    have h := congrFun hlam ⟨w, hw⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Set.restrict_apply] using h
  by_contra hne
  obtain ⟨c₀, hc₀⟩ := not_forall.mp hne
  set A : Finset κ := Finset.univ.filter fun a => ∃ i : Fin (q + 1), lam (a, i) ≠ 0 with hA
  have hAne : A.Nonempty := by
    refine ⟨c₀.1, ?_⟩
    rw [hA, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨c₀.2, hc₀⟩⟩
  obtain ⟨a₀, ha₀, hmax⟩ := A.exists_max_image ord hAne
  set D : ℤ := ord a₀ with hD
  have hstrict : ∀ a ∈ A, a ≠ a₀ → ord a < D := by
    intro a ha hane
    rcases lt_or_eq_of_le (hmax a ha) with h | h
    · exact h
    · exact absurd (hord h) hane
  have hroot : ∀ ζ ∈ Z, ∑ i : Fin (q + 1), lam (a₀, i) * ζ ^ (i : ℕ) = 0 := by
    intro ζ hζ
    obtain ⟨u, t, C, humem, htne, hu, ht, hCne, hlim⟩ := hblow ζ hζ
    set P : κ → ℕ → ℂ := fun a j => ∑ i : Fin (q + 1), lam (a, i) * (u j) ^ (i : ℕ) with hP
    set f : κ → ℕ → ℂ := fun a j =>
      (P a j * (M a (u j) * t j ^ (ord a))) * t j ^ ((D - ord a).toNat) with hf
    have hj : ∀ j, ∑ a ∈ A, f a j = 0 := by
      intro j
      have hstep : ∀ a ∈ A, f a j = t j ^ D * (P a j * M a (u j)) := by
        intro a ha
        have hle : ord a ≤ D := hmax a ha
        have hpow : t j ^ (ord a) * t j ^ ((D - ord a).toNat) = t j ^ D := by
          rw [← zpow_natCast (t j) ((D - ord a).toNat), Int.toNat_of_nonneg (by omega),
            ← zpow_add₀ (htne j)]
          congr 1
          ring
        simp only [hf]
        rw [show (P a j * (M a (u j) * t j ^ (ord a))) * t j ^ ((D - ord a).toNat)
            = (P a j * M a (u j)) * (t j ^ (ord a) * t j ^ ((D - ord a).toNat)) by ring, hpow]
        ring
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
      have hall : ∑ a : κ, P a j * M a (u j) = 0 := by
        have hr := hrel (u j) (humem j)
        rw [Fintype.sum_prod_type] at hr
        rw [← hr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hP, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hvanish : ∀ a ∈ (Finset.univ : Finset κ), a ∉ A → P a j * M a (u j) = 0 := by
        intro a _ haA
        have hzero : ∀ i : Fin (q + 1), lam (a, i) = 0 := by
          by_contra hcon
          have hcon' := not_forall.mp hcon
          exact haA (by rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcon'⟩)
        rw [hP]
        simp [hzero]
      rw [Finset.sum_subset (Finset.subset_univ A) hvanish, hall, mul_zero]
    have hPlim : ∀ a : κ,
        Tendsto (fun j => P a j) atTop (𝓝 (∑ i : Fin (q + 1), lam (a, i) * ζ ^ (i : ℕ))) := by
      intro a
      rw [hP]
      exact tendsto_finsetSum _ fun i _ => ((hu.pow _).const_mul _)
    have hf₀ : Tendsto (f a₀) atTop
        (𝓝 ((∑ i : Fin (q + 1), lam (a₀, i) * ζ ^ (i : ℕ)) * C a₀)) := by
      have hzero : (D - ord a₀).toNat = 0 := by rw [hD]; simp
      simp only [hf, hzero, pow_zero, mul_one]
      exact (hPlim a₀).mul (hlim a₀)
    have hferase : Tendsto (fun j => ∑ a ∈ A.erase a₀, f a j) atTop (𝓝 0) := by
      have hlimzero : ∀ a ∈ A.erase a₀, Tendsto (f a) atTop (𝓝 0) := by
        intro a ha
        have haA : a ∈ A := Finset.mem_of_mem_erase ha
        have hane : a ≠ a₀ := Finset.ne_of_mem_erase ha
        have hpos : 0 < (D - ord a).toNat := by
          have hlt := hstrict a haA hane
          omega
        have htpow : Tendsto (fun j => t j ^ ((D - ord a).toNat)) atTop (𝓝 0) := by
          have hp := ht.pow ((D - ord a).toNat)
          rwa [zero_pow (by omega)] at hp
        have hmul := ((hPlim a).mul (hlim a)).mul htpow
        rw [mul_zero] at hmul
        simp only [hf]
        exact hmul
      have hsum := tendsto_finsetSum (A.erase a₀) hlimzero
      simpa using hsum
    have htotal : Tendsto (fun j => ∑ a ∈ A, f a j) atTop
        (𝓝 ((∑ i : Fin (q + 1), lam (a₀, i) * ζ ^ (i : ℕ)) * C a₀ + 0)) := by
      have hsplit : ∀ j, ∑ a ∈ A, f a j = f a₀ j + ∑ a ∈ A.erase a₀, f a j := by
        intro j
        exact (Finset.add_sum_erase A (fun a => f a j) ha₀).symm
      simp only [hsplit]
      exact hf₀.add hferase
    have hzeroLim : Tendsto (fun j => ∑ a ∈ A, f a j) atTop (𝓝 0) := by
      simp only [hj]
      exact tendsto_const_nhds
    have heq := tendsto_nhds_unique htotal hzeroLim
    rw [add_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_right (hCne a₀)
  set Q : Polynomial ℂ :=
    ∑ i : Fin (q + 1), Polynomial.C (lam (a₀, i)) * Polynomial.X ^ (i : ℕ) with hQ
  have hQzero : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q (hZ.mono ?_)
    intro ζ hζ
    have hev : Q.eval ζ = ∑ i : Fin (q + 1), lam (a₀, i) * ζ ^ (i : ℕ) := by
      rw [hQ, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by simp
    show Q.eval ζ = 0
    rw [hev]
    exact hroot ζ hζ
  have hcoeff : ∀ i : Fin (q + 1), lam (a₀, i) = 0 := by
    intro i
    have h := congrArg (fun p : Polynomial ℂ => p.coeff (i : ℕ)) hQzero
    simp only [hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero] at h
    rw [← h]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have hfalse : ((i : ℕ) = (b : ℕ)) = False := by
        simp only [eq_iff_iff, iff_false]
        intro hcon
        exact hb (Fin.val_injective hcon.symm)
      simp [hfalse]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  rw [hA, Finset.mem_filter] at ha₀
  obtain ⟨-, i, hi⟩ := ha₀
  exact hi (hcoeff i)


/-! ## A family in which one member vanishes -/

/-- The pole model together with the very function that vanishes where it blows up. -/
noncomputable def poleAndZeroPair : Fin 2 → ℂ → ℂ :=
  ![periodicPoleModel, fun w => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) - 1]

/-- **A family with one member of negative order.**  At every integer the first member blows up to
order one and the second vanishes to order one; both leading values are one. -/
theorem integerGradedFamily_poleAndZeroPair :
    IntegerGradedFamily upperHalfPlane poleAndZeroPair (Set.range fun m : ℤ => (m : ℂ))
      ![1, -1] := by
  refine ⟨Set.infinite_range_of_injective (fun x y h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨m, rfl⟩
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach m
  refine ⟨u, fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1, fun _ => 1,
    humem, hne, hlim, hexp, fun a => one_ne_zero, ?_⟩
  intro a
  have hval : ∀ j, poleAndZeroPair a (u j) *
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ ((![1, -1] : Fin 2 → ℤ) a)
      = 1 := by
    intro j
    fin_cases a
    · show periodicPoleModel (u j) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (1 : ℤ) = 1
      rw [zpow_one, periodicPoleModel, inv_mul_cancel₀ (hne j)]
    · show (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (-1 : ℤ) = 1
      rw [zpow_neg_one, mul_inv_cancel₀ (hne j)]
  refine Tendsto.congr (fun j => (hval j).symm) ?_
  fin_cases a <;> simp

/-- **The box of a blowing-up member and a vanishing one is independent.** -/
theorem linearIndependent_degreeBox_poleAndZeroPair (q : ℕ) :
    LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict upperHalfPlane (fun w => w ^ (p.2 : ℕ) * poleAndZeroPair p.1 w)) := by
  refine linearIndependent_restrict_degreeBox_of_integerGraded
    integerGradedFamily_poleAndZeroPair ?_
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

end GaloisForLFunctions.HTGeometry
