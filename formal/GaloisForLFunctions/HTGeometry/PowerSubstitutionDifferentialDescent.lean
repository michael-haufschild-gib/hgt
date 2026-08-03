import GaloisForLFunctions.HTGeometry.PowerSubstitutionJet
import GaloisForLFunctions.HTGeometry.RootOfUnityPacketFilter
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Differential algebraicity descends along `z ↦ z^q`

If the pullback `z ↦ f(z^q)` satisfies an algebraic differential equation, so does `f`.

The proof is elimination, not analytic continuation.  The chain rule of
`PowerSubstitutionJet` turns a jet relation `Q(z, g, g', …, g^{(n)}) = 0` for `g = f(·^q)` into a
relation

`Φ(z, f(z^q), f'(z^q), …, f^{(n)}(z^q)) = 0`,

where `Φ` is the image of `Q` under a substitution that is triangular with invertible diagonal at
every `z ≠ 0`; solving the triangular system shows the substitution is injective, so `Φ ≠ 0`.
Viewing `Φ` as a polynomial in the source point over the jet ring, adjoining the target point as a
new variable `t`, and reducing modulo the monic polynomial `X^q - t` leaves a remainder `ρ` of
degree `< q` which still annihilates the jets along `t = z^q`.  Replacing `z` by `ω^i z` for a
primitive `q`-th root of unity `ω` leaves `z^q` fixed, so the additive root-of-unity filter isolates
a single coefficient of `ρ`; that coefficient, multiplied by the point variable, is an algebraic
differential equation for `f` itself.
-/

namespace HTGeometry

open Polynomial MvPolynomial GaloisForLFunctions

variable {n q : ℕ}

/-! ## The chain-rule substitution on jet variables -/

/-- The jet substitution attached to `z ↦ z^q`.  Slot `0` carries the source point; slot `j+1`
carries the triangular combination `∑_i p_{j,i}(s) · Y_i` supplied by the chain rule, where the
`Y_i` are the jet variables of the target function. -/
noncomputable def powJetSub (q n : ℕ) :
    Fin (n + 2) → Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
  Fin.cases Polynomial.X fun j : Fin (n + 1) =>
    ∑ i : Fin (n + 1),
      (powChainCoeff q (j : ℕ) (i : ℕ)).map
          (algebraMap ℂ (MvPolynomial (Fin (n + 1)) ℂ)) *
        Polynomial.C (MvPolynomial.X i)

@[simp] theorem powJetSub_zero (q n : ℕ) : powJetSub q n 0 = Polynomial.X := rfl

theorem powJetSub_succ (q n : ℕ) (j : Fin (n + 1)) :
    powJetSub q n j.succ =
      ∑ i : Fin (n + 1),
        (powChainCoeff q (j : ℕ) (i : ℕ)).map
            (algebraMap ℂ (MvPolynomial (Fin (n + 1)) ℂ)) *
          Polynomial.C (MvPolynomial.X i) := rfl

/-- Triangularity lets a full jet sum be truncated at the current order. -/
theorem sum_univ_powChainCoeff (q : ℕ) {n : ℕ} (j : Fin (n + 1)) (c : ℕ → ℂ) (z : ℂ) :
    ∑ i : Fin (n + 1), (powChainCoeff q (j : ℕ) (i : ℕ)).eval z * c i
      = ∑ i ∈ Finset.range ((j : ℕ) + 1), (powChainCoeff q (j : ℕ) i).eval z * c i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (powChainCoeff q (j : ℕ) i).eval z * c i) (n + 1)]
  refine (Finset.sum_subset (Finset.range_subset.mpr (by have := j.isLt; omega)) ?_).symm
  intro i _ hi
  rw [powChainCoeff_eq_zero_of_lt q (by simpa using hi)]
  simp

/-- Evaluating the substituted jet slot `j+1` against a jet assignment `b` gives the triangular
combination of `b`. -/
theorem eval₂_powJetSub_succ {n : ℕ} (q : ℕ) (j : Fin (n + 1))
    (g : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) (z : ℂ)
    (hg : ∀ c : ℂ, g (MvPolynomial.C c) = c) :
    Polynomial.eval₂ g z (powJetSub q n j.succ)
      = ∑ i : Fin (n + 1),
          (powChainCoeff q (j : ℕ) (i : ℕ)).eval z * g (MvPolynomial.X i) := by
  rw [powJetSub_succ, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_map, Polynomial.eval₂_C]
  congr 1
  have hid : (g.comp (algebraMap ℂ (MvPolynomial (Fin (n + 1)) ℂ)) : ℂ →+* ℂ) = RingHom.id ℂ := by
    refine RingHom.ext fun c => ?_
    simpa [MvPolynomial.algebraMap_eq] using hg c
  rw [hid, Polynomial.eval₂_id]

/-- A ring homomorphism out of the jet ring that fixes constants evaluates the substituted
polynomial coordinatewise. -/
theorem eval₂_aeval_powJetSub {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) (q : ℕ)
    (g : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) (z : ℂ)
    (hg : ∀ c : ℂ, g (MvPolynomial.C c) = c) :
    Polynomial.eval₂ g z (MvPolynomial.aeval (powJetSub q n) Q)
      = MvPolynomial.eval (fun v => Polynomial.eval₂ g z (powJetSub q n v)) Q := by
  have hcomp : ((Polynomial.eval₂RingHom g z).comp
      (algebraMap ℂ (Polynomial (MvPolynomial (Fin (n + 1)) ℂ))) : ℂ →+* ℂ) = RingHom.id ℂ := by
    refine RingHom.ext fun c => ?_
    simpa [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] using hg c
  have h := MvPolynomial.eval₂_comp_left (Polynomial.eval₂RingHom g z)
    (algebraMap ℂ (Polynomial (MvPolynomial (Fin (n + 1)) ℂ))) (powJetSub q n) Q
  rw [hcomp, MvPolynomial.eval₂_id] at h
  rw [MvPolynomial.aeval_def]
  exact h

/-! ## Injectivity of the substitution -/

/-- The triangular chain-rule system is solvable at every nonzero point: its matrix is lower
triangular with diagonal `(q z^{q-1})^j`, hence invertible. -/
theorem exists_powChainCoeff_solution (hq : 0 < q) {z : ℂ} (hz : z ≠ 0) (n : ℕ)
    (c : Fin (n + 1) → ℂ) :
    ∃ b : Fin (n + 1) → ℂ,
      ∀ j : Fin (n + 1),
        ∑ i : Fin (n + 1), (powChainCoeff q (j : ℕ) (i : ℕ)).eval z * b i = c j := by
  classical
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun j i => (powChainCoeff q (j : ℕ) (i : ℕ)).eval z with hM
  have hlow : M.BlockTriangular ⇑OrderDual.toDual := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := OrderDual.toDual_lt_toDual.mp hij
    simp [hM, powChainCoeff_eq_zero_of_lt q hlt]
  have hbase : ((q : ℂ) * z ^ (q - 1)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hq.ne') (pow_ne_zero _ hz)
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular M hlow]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have hdiag : M i i = ((q : ℂ) * z ^ (q - 1)) ^ (i : ℕ) := by
      simp [hM, powChainCoeff_self]
    rw [hdiag]
    exact pow_ne_zero _ hbase
  refine ⟨M⁻¹.mulVec c, fun j => ?_⟩
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hsolve : M.mulVec (M⁻¹.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  have hj := congrFun hsolve j
  simpa [Matrix.mulVec, dotProduct, hM] using hj

/-- **The chain-rule substitution is injective.**  A nonzero jet relation stays nonzero after
substituting the triangular chain-rule combinations. -/
theorem aeval_powJetSub_ne_zero (hq : 0 < q) {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    (hQ : Q ≠ 0) : MvPolynomial.aeval (powJetSub q n) Q ≠ 0 := by
  intro hzero
  apply hQ
  have hall : ∀ z : ℂ, z ≠ 0 → ∀ c : Fin (n + 1) → ℂ,
      MvPolynomial.eval (Fin.cons z c) Q = 0 := by
    intro z hz c
    obtain ⟨b, hb⟩ := exists_powChainCoeff_solution hq hz n c
    have hg : ∀ d : ℂ, (MvPolynomial.eval b) (MvPolynomial.C d) = d := fun d => by simp
    have h := eval₂_aeval_powJetSub Q q (MvPolynomial.eval b) z hg
    rw [hzero, Polynomial.eval₂_zero] at h
    have hcoord : (fun v => Polynomial.eval₂ (MvPolynomial.eval b) z (powJetSub q n v))
        = Fin.cons z c := by
      funext v
      refine Fin.cases ?_ ?_ v
      · simp
      · intro j
        rw [eval₂_powJetSub_succ q j (MvPolynomial.eval b) z hg, Fin.cons_succ]
        simpa using hb j
    rw [hcoord] at h
    exact h.symm
  have hXQ : (MvPolynomial.X (0 : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) ℂ) * Q = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero, MvPolynomial.eval_X]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · have hcons : Fin.cons (x 0) (fun j : Fin (n + 1) => x j.succ) = x := by
        funext v
        refine Fin.cases ?_ ?_ v <;> simp
      rw [← hcons, hall (x 0) hx _, mul_zero]
  exact (mul_eq_zero.mp hXQ).resolve_left (MvPolynomial.X_ne_zero 0)

/-! ## Descent -/

/-- **Differential algebraicity descends along `z ↦ z^q`.**  If every iterated derivative of `f` is
differentiable and the pullback `z ↦ f(z^q)` satisfies an algebraic differential equation, then so
does `f`. -/
theorem differentiallyAlgebraic_of_comp_pow {f : ℂ → ℂ}
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f)) (hq : 0 < q)
    (h : DifferentiallyAlgebraic (fun z => f (z ^ q))) : DifferentiallyAlgebraic f := by
  classical
  obtain ⟨n, Q, hQ0, hQ⟩ := h
  -- the substituted relation, a polynomial in the source point over the jet ring
  set φ : Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
    MvPolynomial.aeval (powJetSub q n) Q with hφdef
  have hφ0 : φ ≠ 0 := aeval_powJetSub_ne_zero hq hQ0
  set ev : ℂ → MvPolynomial (Fin (n + 1)) ℂ →+* ℂ :=
    fun w => MvPolynomial.eval (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) f w) with hev
  have hevC : ∀ (w : ℂ) (c : ℂ), (ev w) (MvPolynomial.C c) = c := fun w c => by simp [hev]
  have hφrel : ∀ z : ℂ, Polynomial.eval₂ (ev (z ^ q)) z φ = 0 := by
    intro z
    rw [hφdef, eval₂_aeval_powJetSub Q q (ev (z ^ q)) z (hevC (z ^ q))]
    have hcoord : (fun v => Polynomial.eval₂ (ev (z ^ q)) z (powJetSub q n v))
        = Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f (w ^ q)) z) := by
      funext v
      refine Fin.cases ?_ ?_ v
      · simp
      · intro j
        rw [eval₂_powJetSub_succ q j (ev (z ^ q)) z (hevC (z ^ q)), Fin.cons_succ,
          iteratedDeriv_comp_pow hf]
        rw [← sum_univ_powChainCoeff q j (fun i => iteratedDeriv i f (z ^ q)) z]
        exact Finset.sum_congr rfl fun i _ => by simp [hev]
    rw [hcoord]
    exact hQ z
  -- adjoin the target point as a new variable and reduce modulo `X^q - t`
  set φ' : Polynomial (Polynomial (MvPolynomial (Fin (n + 1)) ℂ)) :=
    φ.map (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+* _) with hφ'
  set D : Polynomial (Polynomial (MvPolynomial (Fin (n + 1)) ℂ)) :=
    Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n + 1)) ℂ))
    with hD
  have hDmonic : D.Monic := Polynomial.monic_X_pow_sub_C _ hq.ne'
  set ρ : Polynomial (Polynomial (MvPolynomial (Fin (n + 1)) ℂ)) := φ' %ₘ D with hρdef
  have hsplit : ρ + D * (φ' /ₘ D) = φ' := Polynomial.modByMonic_add_div φ' D
  -- the remainder is nonzero: collapsing `t` to `X^q` kills `D` but restores `φ`
  have hρ0 : ρ ≠ 0 := by
    intro hzero
    apply hφ0
    set inner : Polynomial (MvPolynomial (Fin (n + 1)) ℂ) →+*
        Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
      Polynomial.eval₂RingHom (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+* _)
        (Polynomial.X ^ q) with hinner
    set γ : Polynomial (Polynomial (MvPolynomial (Fin (n + 1)) ℂ)) →+*
        Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
      Polynomial.eval₂RingHom inner Polynomial.X with hγ
    have hγD : γ D = 0 := by
      simp [hγ, hD, hinner]
    have hγφ' : γ φ' = φ := by
      have hcompC : (inner.comp (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+* _))
          = (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+* _) := by
        refine RingHom.ext fun b => ?_
        simp [hinner]
      calc γ φ' = Polynomial.eval₂ inner Polynomial.X (φ.map Polynomial.C) := by
            simp [hγ, hφ']
        _ = Polynomial.eval₂ (inner.comp Polynomial.C) Polynomial.X φ := Polynomial.eval₂_map _ _ _
        _ = Polynomial.eval₂ Polynomial.C Polynomial.X φ := by rw [hcompC]
        _ = φ := Polynomial.eval₂_C_X
    have : γ φ' = 0 := by
      rw [← hsplit, hzero, zero_add, map_mul, hγD, zero_mul]
    rwa [hγφ'] at this
  -- degree bound
  have hdeg : ρ.natDegree < q := by
    have h1 : ρ.degree < D.degree := by
      rw [hρdef]; exact Polynomial.degree_modByMonic_lt φ' hDmonic
    rw [hD, Polynomial.degree_X_pow_sub_C hq] at h1
    exact (Polynomial.natDegree_lt_iff_degree_lt hρ0).mpr h1
  -- the remainder still annihilates the jets along `t = z^q`
  set E : ℂ → Polynomial (MvPolynomial (Fin (n + 1)) ℂ) →+* ℂ :=
    fun w => Polynomial.eval₂RingHom (ev w) w with hE
  have hEC : ∀ (w : ℂ) (b : MvPolynomial (Fin (n + 1)) ℂ), (E w) (Polynomial.C b) = (ev w) b :=
    fun w b => by simp [hE]
  have hErel : ∀ z : ℂ, Polynomial.eval₂ (E (z ^ q)) z ρ = 0 := by
    intro z
    have hD0 : Polynomial.eval₂ (E (z ^ q)) z D = 0 := by
      simp [hD, hE]
    have hφ'0 : Polynomial.eval₂ (E (z ^ q)) z φ' = 0 := by
      have hcompC : ((E (z ^ q)).comp (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+* _))
          = ev (z ^ q) := by
        refine RingHom.ext fun b => ?_
        exact hEC (z ^ q) b
      calc Polynomial.eval₂ (E (z ^ q)) z φ'
          = Polynomial.eval₂ (E (z ^ q)) z (φ.map Polynomial.C) := by rw [hφ']
        _ = Polynomial.eval₂ ((E (z ^ q)).comp Polynomial.C) z φ := Polynomial.eval₂_map _ _ _
        _ = Polynomial.eval₂ (ev (z ^ q)) z φ := by rw [hcompC]
        _ = 0 := hφrel z
    have := congrArg (Polynomial.eval₂ (E (z ^ q)) z) hsplit
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hD0, zero_mul, add_zero, hφ'0] at this
    exact this
  -- root-of-unity filter isolating the top coefficient of the remainder
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω q :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / q), Complex.isPrimitiveRoot_exp q hq.ne'⟩
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hcoeff : ρ.coeff ρ.natDegree ≠ 0 := by
    simpa [Polynomial.leadingCoeff] using Polynomial.leadingCoeff_ne_zero.mpr hρ0
  have hfilter : ∀ z : ℂ, z ^ ρ.natDegree * (E (z ^ q)) (ρ.coeff ρ.natDegree) = 0 := by
    intro z
    have hexp : ∀ i : ℕ,
        ∑ s ∈ Finset.range q, (E (z ^ q)) (ρ.coeff s) * (ω ^ i * z) ^ s = 0 := by
      intro i
      have hpow : (ω ^ i * z) ^ q = z ^ q := by
        rw [mul_pow, ← pow_mul, mul_comm i q, pow_mul, hω.pow_eq_one, one_pow, one_mul]
      have h1 := hErel (ω ^ i * z)
      rw [hpow] at h1
      rw [← h1]
      exact (Polynomial.eval₂_eq_sum_range' (E (z ^ q)) hdeg (ω ^ i * z)).symm
    have hzero : ∑ i ∈ Finset.range q,
        ω ^ (i * (q - ρ.natDegree)) *
          (∑ s ∈ Finset.range q, (E (z ^ q)) (ρ.coeff s) * (ω ^ i * z) ^ s) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hexp i, mul_zero]
    have hswap : ∑ i ∈ Finset.range q,
        ω ^ (i * (q - ρ.natDegree)) *
          (∑ s ∈ Finset.range q, (E (z ^ q)) (ρ.coeff s) * (ω ^ i * z) ^ s)
        = ∑ s ∈ Finset.range q,
            (E (z ^ q)) (ρ.coeff s) * z ^ s *
              (if q ∣ (s + (q - ρ.natDegree)) then (q : ℂ) else 0) := by
      rw [Finset.sum_comm']
      · refine Finset.sum_congr rfl fun s _ => ?_
        rw [← sum_primitiveRoot_pow_mul hω (s + (q - ρ.natDegree)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, ← pow_mul, mul_add, pow_add, mul_comm i s]
        ring
      · intro i s
        simp
    rw [hswap] at hzero
    have hsingle : ∑ s ∈ Finset.range q,
        (E (z ^ q)) (ρ.coeff s) * z ^ s *
          (if q ∣ (s + (q - ρ.natDegree)) then (q : ℂ) else 0)
        = (E (z ^ q)) (ρ.coeff ρ.natDegree) * z ^ ρ.natDegree * (q : ℂ) := by
      refine Finset.sum_eq_single ρ.natDegree ?_ ?_
      · intro s hs hsr
        have hslt : s < q := Finset.mem_range.mp hs
        have hnot : ¬ q ∣ (s + (q - ρ.natDegree)) := by
          rintro ⟨k, hk⟩
          have hk0 : k ≠ 0 := by
            rintro rfl
            simp only [Nat.mul_zero] at hk
            omega
          have hk2 : k < 2 := by
            by_contra hcon
            push_neg at hcon
            have hle : q * 2 ≤ q * k := Nat.mul_le_mul_left q hcon
            omega
          have hk1 : k = 1 := by omega
          subst hk1
          simp only [Nat.mul_one] at hk
          omega
        rw [if_neg hnot, mul_zero]
      · intro hnm
        exact absurd (Finset.mem_range.mpr hdeg) hnm
    rw [hsingle] at hzero
    have := mul_eq_zero.mp hzero
    rcases this with h | h
    · rw [← h]; ring
    · exact absurd h hqC
  -- assemble the descended relation
  refine ⟨n, (MvPolynomial.finSuccEquiv ℂ (n + 1)).symm
    (Polynomial.X * ρ.coeff ρ.natDegree), ?_, ?_⟩
  · intro hcon
    have hXc : (Polynomial.X : Polynomial (MvPolynomial (Fin (n + 1)) ℂ)) *
        ρ.coeff ρ.natDegree = 0 := by
      have := congrArg (MvPolynomial.finSuccEquiv ℂ (n + 1)) hcon
      simpa using this
    rcases mul_eq_zero.mp hXc with h | h
    · exact Polynomial.X_ne_zero h
    · exact hcoeff h
  · intro w
    have hbridge : MvPolynomial.eval
        (Fin.cons w (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) f w))
        ((MvPolynomial.finSuccEquiv ℂ (n + 1)).symm
          (Polynomial.X * ρ.coeff ρ.natDegree))
        = (E w) (Polynomial.X * ρ.coeff ρ.natDegree) := by
      rw [MvPolynomial.eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply]
      rw [← Polynomial.eval₂_eq_eval_map]
      rfl
    rw [show (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)
        = (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) f w) from rfl, hbridge]
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ q = w := IsAlgClosed.exists_pow_nat_eq w hq
    have hval : (E w) (Polynomial.X * ρ.coeff ρ.natDegree)
        = w * (E w) (ρ.coeff ρ.natDegree) := by
      rw [map_mul]
      congr 1
      simp [hE]
    rw [hval]
    by_cases hz0 : z = 0
    · rw [← hz, hz0, zero_pow hq.ne', zero_mul]
    · have hf := hfilter z
      rw [hz] at hf
      have hzr : z ^ ρ.natDegree ≠ 0 := pow_ne_zero _ hz0
      rcases mul_eq_zero.mp hf with h | h
      · exact absurd h hzr
      · rw [h, mul_zero]

end HTGeometry
