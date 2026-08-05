import GaloisForLFunctions.HTGeometry.BoxBasisTransport

/-!
# The orders may vary from point to point

The graded law asks for one order function serving every point of the infinite set.  That is more
than the argument uses.  At each point the proof only needs a *dominant* member of the support, and
which member dominates may change from point to point: the support is finite and the set of points
is infinite, so one member dominates infinitely often, and that is enough to make its degree block a
polynomial with infinitely many roots.

This matters because pole orders of a fixed family genuinely differ from pole to pole.  A family
whose orders collide at some points but are separated at infinitely many others is now decided.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A family that is graded at each point of `Z`, with the chart, the orders and the leading values
all allowed to depend on the point. -/
def PointwiseGradedFamily {κ : Type*} (S : Set ℂ) (M : κ → ℂ → ℂ) (Z : Set ℂ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u t : ℕ → ℂ) (C : κ → ℂ) (ord : κ → ℕ),
    (∀ j, u j ∈ S) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      Function.Injective ord ∧ (∀ a, C a ≠ 0) ∧
      ∀ a, Tendsto (fun j => M a (u j) * t j ^ (ord a)) atTop (𝓝 (C a))

/-- **Pointwise distinct orders decide the degree box.**  At each point some member of the support
dominates; the support is finite and the point set infinite, so one member dominates infinitely
often and its degree block vanishes identically. -/
theorem linearIndependent_restrict_degreeBox_of_pointwiseGraded
    {κ : Type*} [Fintype κ] [DecidableEq κ] {q : ℕ} {S : Set ℂ} {M : κ → ℂ → ℂ}
    {Z : Set ℂ} (hdata : PointwiseGradedFamily S M Z) :
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
  have hkey : ∀ ζ : Z, ∃ a ∈ A, ∑ i : Fin (q + 1), lam (a, i) * (ζ : ℂ) ^ (i : ℕ) = 0 := by
    intro ζ
    obtain ⟨u, t, C, ord, humem, hu, ht, hordinj, hCne, hlim⟩ := hblow ζ ζ.2
    obtain ⟨a₀, ha₀, hmax⟩ := A.exists_max_image ord hAne
    refine ⟨a₀, ha₀, ?_⟩
    set D : ℕ := ord a₀ with hD
    have hstrict : ∀ a ∈ A, a ≠ a₀ → ord a < D := by
      intro a ha hane
      rcases lt_or_eq_of_le (hmax a ha) with h | h
      · exact h
      · exact absurd (hordinj h) hane
    set P : κ → ℕ → ℂ := fun a j => ∑ i : Fin (q + 1), lam (a, i) * (u j) ^ (i : ℕ) with hP
    set f : κ → ℕ → ℂ := fun a j =>
      (P a j * (M a (u j) * t j ^ (ord a))) * t j ^ (D - ord a) with hf
    have hj : ∀ j, ∑ a ∈ A, f a j = 0 := by
      intro j
      have hstep : ∀ a ∈ A, f a j = t j ^ D * (P a j * M a (u j)) := by
        intro a ha
        have hle : ord a ≤ D := hmax a ha
        simp only [hf]
        rw [show (P a j * (M a (u j) * t j ^ (ord a))) * t j ^ (D - ord a)
            = (P a j * M a (u j)) * (t j ^ (ord a) * t j ^ (D - ord a)) by ring,
          ← pow_add, Nat.add_sub_cancel' hle]
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
        Tendsto (fun j => P a j) atTop
          (𝓝 (∑ i : Fin (q + 1), lam (a, i) * (ζ : ℂ) ^ (i : ℕ))) := by
      intro a
      rw [hP]
      exact tendsto_finsetSum _ fun i _ => ((hu.pow _).const_mul _)
    have hf₀ : Tendsto (f a₀) atTop
        (𝓝 ((∑ i : Fin (q + 1), lam (a₀, i) * (ζ : ℂ) ^ (i : ℕ)) * C a₀)) := by
      have hzero : D - ord a₀ = 0 := by rw [hD]; omega
      simp only [hf, hzero, pow_zero, mul_one]
      exact (hPlim a₀).mul (hlim a₀)
    have hferase : Tendsto (fun j => ∑ a ∈ A.erase a₀, f a j) atTop (𝓝 0) := by
      have hlimzero : ∀ a ∈ A.erase a₀, Tendsto (f a) atTop (𝓝 0) := by
        intro a ha
        have haA : a ∈ A := Finset.mem_of_mem_erase ha
        have hane : a ≠ a₀ := Finset.ne_of_mem_erase ha
        have hpos : 0 < D - ord a := by
          have := hstrict a haA hane
          omega
        have htpow : Tendsto (fun j => t j ^ (D - ord a)) atTop (𝓝 0) := by
          have hp := ht.pow (D - ord a)
          rwa [zero_pow (by omega)] at hp
        have hmul := ((hPlim a).mul (hlim a)).mul htpow
        rw [mul_zero] at hmul
        simp only [hf]
        exact hmul
      have hsum := tendsto_finsetSum (A.erase a₀) hlimzero
      simpa using hsum
    have htotal : Tendsto (fun j => ∑ a ∈ A, f a j) atTop
        (𝓝 ((∑ i : Fin (q + 1), lam (a₀, i) * (ζ : ℂ) ^ (i : ℕ)) * C a₀ + 0)) := by
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
  choose dom hdomA hdomZero using hkey
  haveI : Infinite (Z : Set ℂ) := Set.infinite_coe_iff.mpr hZ
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber dom
  have hfib : (dom ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  have himg : (Subtype.val '' (dom ⁻¹' {y})).Infinite :=
    hfib.image (Subtype.val_injective.injOn)
  set Q : Polynomial ℂ :=
    ∑ i : Fin (q + 1), Polynomial.C (lam (y, i)) * Polynomial.X ^ (i : ℕ) with hQ
  have hQzero : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q (himg.mono ?_)
    rintro z ⟨ζ, hζ, rfl⟩
    have hyz : dom ζ = y := hζ
    have hev : Q.eval (ζ : ℂ) = ∑ i : Fin (q + 1), lam (y, i) * (ζ : ℂ) ^ (i : ℕ) := by
      rw [hQ, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by simp
    show Q.eval (ζ : ℂ) = 0
    rw [hev, ← hyz]
    exact hdomZero ζ
  have hcoeff : ∀ i : Fin (q + 1), lam (y, i) = 0 := by
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
  obtain ⟨ζ₀, hζ₀⟩ := hfib.nonempty
  have hyA : y ∈ A := by
    have := hdomA ζ₀
    rwa [show dom ζ₀ = y from hζ₀] at this
  rw [hA, Finset.mem_filter] at hyA
  obtain ⟨-, i, hi⟩ := hyA
  exact hi (hcoeff i)

/-- The graded law is the case of a point-independent order function. -/
theorem pointwiseGradedFamily_of_gradedBlowUp {κ : Type*} {S : Set ℂ} {M : κ → ℂ → ℂ}
    {Z : Set ℂ} {ord : κ → ℕ} (hdata : GradedBlowUpFamily S M Z ord)
    (hord : Function.Injective ord) : PointwiseGradedFamily S M Z := by
  obtain ⟨hZ, hblow⟩ := hdata
  refine ⟨hZ, ?_⟩
  intro ζ hζ
  obtain ⟨u, t, C, humem, hu, ht, hCne, hlim⟩ := hblow ζ hζ
  exact ⟨u, t, C, ord, humem, hu, ht, hord, hCne, hlim⟩

end GaloisForLFunctions.HTGeometry
