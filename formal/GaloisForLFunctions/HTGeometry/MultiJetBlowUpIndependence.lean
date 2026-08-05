import GaloisForLFunctions.HTGeometry.PoleJetAlgebraicIndependence

/-!
# Several jets, several blow-up rates

The single-jet blow-up law forbids the coordinate from entering an algebraic relation with one
blowing-up function.  With several jets a relation can hide in a cancellation between monomials of
equal blow-up order — the phenomenon that makes `L² − L'` drop order for a Cauchy transform — so the
order alone cannot separate them.

The obstruction disappears once the target is the one actually needed: not full algebraic
independence, but linear independence of a *bounded* monomial box.  There the exponents range over a
finite set, and a rate vector separating that finite set on the nose is enough.  The dominant
stratum is then a single monomial; dividing by the common scale and passing to the limit turns the
relation into a polynomial identity in the limit point, and the limit points are infinite in number.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## Order bookkeeping -/

/-- The blow-up order of a jet monomial when the jets blow up at prescribed rates. -/
def blowUpOrder {n : ℕ} (d : Fin n → ℕ) (e : Fin n →₀ ℕ) : ℕ :=
  e.sum fun k m => m * d k

theorem prod_mul_pow_eq_prod_mul_pow_order {n : ℕ} (d : Fin n → ℕ) (e : Fin n →₀ ℕ)
    (G : Fin n → ℂ) (t : ℂ) :
    ∏ k ∈ e.support, (G k * t ^ (d k)) ^ (e k)
      = (∏ k ∈ e.support, (G k) ^ (e k)) * t ^ (blowUpOrder d e) := by
  rw [Finset.prod_congr rfl fun k _ => mul_pow (G k) (t ^ d k) (e k), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_congr rfl fun k _ => (pow_mul t (d k) (e k)).symm,
    Finset.prod_pow_eq_pow_sum, blowUpOrder, Finsupp.sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Nat.mul_comm _ _

/-! ## Blow-up data with prescribed rates -/

/-- At each point of an infinite set the jets blow up against a common vanishing scale at prescribed
rates, with nonzero leading values. -/
def MultiBlowUpData {n : ℕ} (S : Set ℂ) (F : Fin n → ℂ → ℂ) (Z : Set ℂ) (d : Fin n → ℕ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (c : Fin n → ℂ),
    (∀ j, u j ∈ S) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k, c k ≠ 0) ∧
      ∀ k, Tendsto (fun j => F k (u j) * t j ^ (d k)) atTop (𝓝 (c k))

/-! ## The multi-jet law -/

/-- A family with prescribed blow-up orders and nonzero leading values. -/
def GradedBlowUpFamily {κ : Type*} (S : Set ℂ) (M : κ → ℂ → ℂ) (Z : Set ℂ) (ord : κ → ℕ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (C : κ → ℂ),
    (∀ j, u j ∈ S) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ a, C a ≠ 0) ∧ ∀ a, Tendsto (fun j => M a (u j) * t j ^ (ord a)) atTop (𝓝 (C a))

/-- **Distinct blow-up orders make a degree box independent.**  The monomial structure of the family
plays no role: only the orders and the nonvanishing of the leading values.  The dominant stratum of a
relation is a single member, and dividing by the common scale turns the relation into a polynomial
vanishing at infinitely many points. -/
theorem linearIndependent_restrict_degreeBox_of_gradedBlowUp
    {κ : Type*} [Fintype κ] [DecidableEq κ] {q : ℕ} {S : Set ℂ} {M : κ → ℂ → ℂ}
    {Z : Set ℂ} {ord : κ → ℕ} (hdata : GradedBlowUpFamily S M Z ord)
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
  set D : ℕ := ord a₀ with hD
  have hstrict : ∀ a ∈ A, a ≠ a₀ → ord a < D := by
    intro a ha hane
    rcases lt_or_eq_of_le (hmax a ha) with h | h
    · exact h
    · exact absurd (hord h) hane
  have hroot : ∀ ζ ∈ Z, ∑ i : Fin (q + 1), lam (a₀, i) * ζ ^ (i : ℕ) = 0 := by
    intro ζ hζ
    obtain ⟨u, t, C, humem, hu, ht, hCne, hlim⟩ := hblow ζ hζ
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
        Tendsto (fun j => P a j) atTop (𝓝 (∑ i : Fin (q + 1), lam (a, i) * ζ ^ (i : ℕ))) := by
      intro a
      rw [hP]
      exact tendsto_finsetSum _ fun i _ => ((hu.pow _).const_mul _)
    have hf₀ : Tendsto (f a₀) atTop
        (𝓝 ((∑ i : Fin (q + 1), lam (a₀, i) * ζ ^ (i : ℕ)) * C a₀)) := by
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

/-- A jet monomial family with separated rates is a graded blow-up family. -/
theorem gradedBlowUpFamily_of_multiBlowUp {κ : Type*} {n : ℕ} {S : Set ℂ} {F : Fin n → ℂ → ℂ}
    {Z : Set ℂ} {d : Fin n → ℕ} (hdata : MultiBlowUpData S F Z d)
    (exponent : κ → (Fin n →₀ ℕ)) :
    GradedBlowUpFamily S (fun a w => ∏ k ∈ (exponent a).support, (F k w) ^ (exponent a k)) Z
      (fun a => blowUpOrder d (exponent a)) := by
  obtain ⟨hZ, hblow⟩ := hdata
  refine ⟨hZ, ?_⟩
  intro ζ hζ
  obtain ⟨u, t, c, humem, hu, ht, hcne, hlim⟩ := hblow ζ hζ
  refine ⟨u, t, fun a => ∏ k ∈ (exponent a).support, (c k) ^ (exponent a k),
    humem, hu, ht, ?_, ?_⟩
  · intro a
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hcne k)
  · intro a
    have hprod := tendsto_finsetProd (M := ℂ) (exponent a).support
      (f := fun k j => (F k (u j) * t j ^ (d k)) ^ (exponent a k))
      (a := fun k => (c k) ^ (exponent a k)) (fun k _ => (hlim k).pow _)
    refine hprod.congr fun j => ?_
    exact prod_mul_pow_eq_prod_mul_pow_order d (exponent a) (fun k => F k (u j)) (t j)

/-- **Separated blow-up rates make the expanded monomial box independent.**  The monomial case of
the graded law. -/
theorem linearIndependent_restrict_expandedMonomialFamily_of_multiBlowUp
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} {S : Set ℂ} {F : Fin n → ℂ → ℂ}
    {Z : Set ℂ} {d : Fin n → ℕ} (hdata : MultiBlowUpData S F Z d)
    {exponent : κ → (Fin n →₀ ℕ)}
    (hord : Function.Injective fun a => blowUpOrder d (exponent a)) :
    LinearIndependent ℂ
      (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c)) := by
  have hgen := linearIndependent_restrict_degreeBox_of_gradedBlowUp (q := q)
    (gradedBlowUpFamily_of_multiBlowUp hdata exponent) hord
  have hfam : (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c))
      = (fun p : κ × Fin (q + 1) => Set.restrict S
          (fun w => w ^ (p.2 : ℕ) * ∏ k ∈ (exponent p.1).support, (F k w) ^ (exponent p.1 k))) := by
    funext p x
    exact expandedMonomialFamily_apply F exponent p (x : ℂ)
  rw [hfam]
  exact hgen

/-! ## A realization with arbitrarily many jets -/

/-- **Powers of the pole model realize the multi-jet datum at any rate vector.**  Along the vertical
approach the pole model is exactly the reciprocal of the vanishing scale, so each power blows up at
exactly its own rate with leading value one. -/
theorem multiBlowUpData_periodicPolePowers {n : ℕ} (a : Fin n → ℕ) :
    MultiBlowUpData upperHalfPlane (fun k w => periodicPoleModel w ^ a k)
      (Set.range fun m : ℤ => (m : ℂ)) a := by
  refine ⟨Set.infinite_range_of_injective (fun x y h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨m, rfl⟩
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach m
  refine ⟨u, fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1, fun _ => 1,
    humem, hlim, hexp, fun _ => one_ne_zero, ?_⟩
  intro k
  have hone : ∀ j : ℕ,
      (periodicPoleModel (u j)) ^ (a k) *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (a k) = 1 := by
    intro j
    rw [← mul_pow, periodicPoleModel, inv_mul_cancel₀ (hne j), one_pow]
  exact tendsto_const_nhds.congr fun j => (hone j).symm

/-- **The full-rank datum with arbitrarily many jets.**  A rate vector separating the exponent family
delivers the node packet in the upper half-plane. -/
theorem exists_row_packet_upperHalfPlane_of_multiBlowUp {κ row : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype row] {n q : ℕ} {S : Set ℂ} {F : Fin n → ℂ → ℂ} {Z : Set ℂ}
    {d : Fin n → ℕ} (hS : S.Infinite) (hdata : MultiBlowUpData S F Z d)
    {exponent : κ → (Fin n →₀ ℕ)}
    (hord : Function.Injective fun a => blowUpOrder d (exponent a))
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, z b ∈ S) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  obtain ⟨z₀, hz₀mem, hz₀inj, hz₀rank⟩ :=
    exists_node_packet_mem_mulVec_injective (q := q) F exponent S
      (linearIndependent_restrict_expandedMonomialFamily_of_multiBlowUp hdata hord)
  obtain ⟨z, hzinj, hzmem, hzext⟩ :=
    exists_injective_extension_mem f hf hS z₀ hz₀inj hz₀mem
  refine ⟨z, hzmem, hzinj, ?_⟩
  refine mulVec_injective_of_submatrix_row _ f ?_
  have hsub :
      (expandedDifferentialEvaluationMatrix q n z exponent
          (fun p => F p.2 (z p.1))).submatrix f id
        = expandedDifferentialEvaluationMatrix q n z₀ exponent (fun p => F p.2 (z₀ p.1)) := by
    ext b c
    simp only [Matrix.submatrix_apply, id_eq]
    simp only [expandedDifferentialEvaluationMatrix, hzext]
  rw [hsub]
  exact hz₀rank

end GaloisForLFunctions.HTGeometry
