import GaloisForLFunctions.HTGeometry.ExpandedEvaluationRowExtension

/-!
# Periodicity adjoins the coordinate for free

Algebraic independence of a jet family says nothing, by itself, about the coordinate: a family may
be independent while satisfying a relation once the coordinate is allowed in.  Periodicity forbids
that.  On a region stable under a nonzero translation, along which every jet is invariant, any
algebraic relation involving the coordinate is a polynomial in the coordinate whose coefficients are
constant along the translation orbit; the orbit is infinite, so the polynomial vanishes identically
and the relation was a relation among the jets alone.

Hence a periodic jet family that is algebraically independent stays independent after the coordinate
is adjoined — exactly the datum the expanded evaluation layer requires.  The exponential realizes it
unconditionally.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {S : Set ℂ}

/-! ## The translation and its invariants -/

/-- Translation of a translation-stable region. -/
def regionShift (a : ℂ) (hS : ∀ w ∈ S, w + a ∈ S) (w : S) : S := ⟨w + a, hS w w.2⟩

theorem coe_regionShift_iterate (a : ℂ) (hS : ∀ w ∈ S, w + a ∈ S) (w : S) (m : ℕ) :
    (((regionShift a hS)^[m] w : S) : ℂ) = (w : ℂ) + m * a := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      show ((regionShift a hS)^[m] w : ℂ) + a = (w : ℂ) + ((m + 1 : ℕ) : ℂ) * a
      rw [ih]
      push_cast
      ring

/-- Precomposition with the translation, as an algebra map on functions of the region. -/
def regionShiftAlgHom (a : ℂ) (hS : ∀ w ∈ S, w + a ∈ S) : (S → ℂ) →ₐ[ℂ] (S → ℂ) where
  toFun g := g ∘ regionShift a hS
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The subalgebra of functions on the region invariant under the translation. -/
def regionPeriodicSubalgebra (a : ℂ) (hS : ∀ w ∈ S, w + a ∈ S) : Subalgebra ℂ (S → ℂ) :=
  AlgHom.equalizer (regionShiftAlgHom a hS) (AlgHom.id ℂ (S → ℂ))

theorem mem_regionPeriodicSubalgebra_iff {a : ℂ} {hS : ∀ w ∈ S, w + a ∈ S} {g : S → ℂ} :
    g ∈ regionPeriodicSubalgebra a hS ↔ ∀ w : S, g (regionShift a hS w) = g w := by
  constructor
  · intro h w
    exact congrFun h w
  · intro h
    funext w
    exact h w

theorem apply_iterate_eq_of_mem_regionPeriodicSubalgebra {a : ℂ} {hS : ∀ w ∈ S, w + a ∈ S}
    {g : S → ℂ} (hg : g ∈ regionPeriodicSubalgebra a hS) (w : S) (m : ℕ) :
    g ((regionShift a hS)^[m] w) = g w := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', mem_regionPeriodicSubalgebra_iff.mp hg, ih]

/-! ## The translation orbit kills a polynomial -/

theorem eq_zero_of_eval_translate_orbit {a : ℂ} (ha : a ≠ 0)
    (w : S) (R : ℂ[X]) (h : ∀ m : ℕ, R.eval ((w : ℂ) + m * a) = 0) : R = 0 := by
  refine eq_zero_of_infinite_isRoot R ?_
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (w : ℂ) + m * a) ?_ ?_
  · intro m₁ m₂ hm
    have h1 : (m₁ : ℂ) * a = (m₂ : ℂ) * a := add_left_cancel hm
    have hcast : (m₁ : ℂ) = (m₂ : ℂ) := mul_right_cancel₀ ha h1
    exact_mod_cast hcast
  · intro m
    exact h m


/-! ## The coordinate is transcendental over the periodic jets -/

/-- **The coordinate is transcendental over any algebra of translation-invariant functions.**  A
polynomial relation with invariant coefficients is constant along the translation orbit, and the
orbit is infinite. -/
theorem transcendental_coe_of_periodic {n : ℕ} {F : Fin n → ℂ → ℂ} {a : ℂ} (ha : a ≠ 0)
    (hS : ∀ w ∈ S, w + a ∈ S) (hper : ∀ k, ∀ w ∈ S, F k (w + a) = F k w) :
    Transcendental (↥(Algebra.adjoin ℂ (Set.range (fun k => Set.restrict S (F k)))))
      (fun w : S => (w : ℂ)) := by
  set A := Algebra.adjoin ℂ (Set.range (fun k => Set.restrict S (F k))) with hA
  have hle : A ≤ regionPeriodicSubalgebra a hS := by
    rw [hA]
    refine Algebra.adjoin_le ?_
    rintro g ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_regionPeriodicSubalgebra_iff]
    intro w
    exact hper k w w.2
  rintro ⟨p, hp0, hp⟩
  set ev : S → (↥A →+* ℂ) := fun v =>
    (Pi.evalRingHom (fun _ : S => ℂ) v).comp (algebraMap (↥A) (S → ℂ)) with hev
  have hevapp : ∀ (v : S) (c : ↥A), ev v c = (c : S → ℂ) v := fun _ _ => rfl
  have key : ∀ v : S, (p.map (ev v)).eval ((v : ℂ)) = 0 := by
    intro v
    have h := congrFun hp v
    rw [Polynomial.aeval_def] at h
    have hcomm := Polynomial.hom_eval₂ p (algebraMap (↥A) (S → ℂ))
      (Pi.evalRingHom (fun _ : S => ℂ) v) (fun w : S => (w : ℂ))
    rw [Polynomial.eval_map]
    calc Polynomial.eval₂ (ev v) ((v : ℂ)) p
        = (Pi.evalRingHom (fun _ : S => ℂ) v)
            (Polynomial.eval₂ (algebraMap (↥A) (S → ℂ)) (fun w : S => (w : ℂ)) p) := hcomm.symm
      _ = 0 := h
  refine hp0 (Polynomial.ext fun i => ?_)
  rw [Polynomial.coeff_zero]
  refine Subtype.ext (funext fun w => ?_)
  have hconst : ∀ (m : ℕ), p.map (ev ((regionShift a hS)^[m] w)) = p.map (ev w) := by
    intro m
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hevapp, hevapp]
    exact apply_iterate_eq_of_mem_regionPeriodicSubalgebra (hle (p.coeff j).2) w m
  have hroots : ∀ m : ℕ, (p.map (ev w)).eval ((w : ℂ) + m * a) = 0 := by
    intro m
    rw [← coe_regionShift_iterate a hS w m, ← hconst m]
    exact key _
  have hzero := eq_zero_of_eval_translate_orbit ha w _ hroots
  have := congrArg (fun r : ℂ[X] => r.coeff i) hzero
  rw [Polynomial.coeff_map, hevapp] at this
  simpa using this


/-! ## Periodicity adjoins the coordinate -/

/-- **Periodicity upgrades algebraic independence of a jet family to independence with the
coordinate adjoined.**  On a region stable under a nonzero translation along which every jet is
invariant, no algebraic relation can involve the coordinate. -/
theorem algebraicIndependent_restrict_jetEvaluationFamily_of_periodic
    {n : ℕ} {F : Fin n → ℂ → ℂ} {a : ℂ} (ha : a ≠ 0) (hS : ∀ w ∈ S, w + a ∈ S)
    (hper : ∀ k, ∀ w ∈ S, F k (w + a) = F k w)
    (hind : AlgebraicIndependent ℂ (fun k => Set.restrict S (F k))) :
    AlgebraicIndependent ℂ (fun i => Set.restrict S (jetEvaluationFamily F i)) := by
  have hfam : (fun i => Set.restrict S (jetEvaluationFamily F i))
      = fun o : Option (Fin n) =>
          o.elim (fun w : S => (w : ℂ)) (fun k => Set.restrict S (F k)) := by
    funext i
    cases i with
    | none => rfl
    | some k => rfl
  rw [hfam]
  exact AlgebraicIndependent.option_iff.mpr ⟨hind, transcendental_coe_of_periodic ha hS hper⟩

/-! ## The exponential realizes the datum -/

theorem eval_of_aeval_pi_eq_zero {ι : Type*} {g : ι → ℂ} {q : ℂ[X]}
    (h : Polynomial.aeval g q = 0) (i : ι) : q.eval (g i) = 0 := by
  have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : ι => ℂ) i) g q
  rw [h] at this
  rw [Polynomial.coe_aeval_eq_eval] at this
  simpa using this

/-- The exponential is transcendental over the constants on the upper half-plane: its values along a
horizontal line already have infinitely many distinct moduli. -/
theorem transcendental_restrict_exp_upperHalfPlane :
    Transcendental ℂ (Set.restrict upperHalfPlane Complex.exp) := by
  rintro ⟨q, hq0, hq⟩
  refine hq0 (Polynomial.eq_zero_of_infinite_isRoot q ?_)
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℝ => Complex.exp ((t : ℂ) + Complex.I)) ?_ ?_
  · intro t₁ t₂ ht
    have hnorm : Real.exp (((t₁ : ℂ) + Complex.I).re) = Real.exp (((t₂ : ℂ) + Complex.I).re) := by
      rw [← Complex.norm_exp, ← Complex.norm_exp]
      exact congrArg (fun z : ℂ => ‖z‖) ht
    simpa using Real.exp_eq_exp.mp hnorm
  · intro t
    have hmem : ((t : ℂ) + Complex.I) ∈ upperHalfPlane := by
      simp [upperHalfPlane]
    exact eval_of_aeval_pi_eq_zero hq ⟨_, hmem⟩

/-- **The full-rank datum is realized.**  The coordinate together with the exponential is
algebraically independent over the constants on the upper half-plane. -/
theorem algebraicIndependent_restrict_jetEvaluationFamily_exp :
    AlgebraicIndependent ℂ
      (fun i => Set.restrict upperHalfPlane (jetEvaluationFamily ![Complex.exp] i)) := by
  refine algebraicIndependent_restrict_jetEvaluationFamily_of_periodic
    (a := 2 * (Real.pi : ℂ) * Complex.I) ?_ ?_ ?_ ?_
  · simp [Real.pi_ne_zero, Complex.I_ne_zero]
  · intro w hw
    have : (0 : ℝ) < w.im := hw
    have himd : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
      simp
    show 0 < (w + 2 * (Real.pi : ℂ) * Complex.I).im
    rw [Complex.add_im, himd]
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    linarith
  · intro k w _
    have hk : ![Complex.exp] k = Complex.exp := by fin_cases k; rfl
    rw [hk]
    exact Complex.exp_periodic w
  · rw [algebraicIndependent_unique_type_iff]
    exact transcendental_restrict_exp_upperHalfPlane


/-- **Unconditional realization of the full-rank datum.**  For every injectively indexed exponent
family and every row family large enough to carry the columns, a node packet exists in the upper
half-plane, with pairwise distinct nodes, on which the expanded evaluation map is injective. -/
theorem exists_row_packet_upperHalfPlane_exp {κ row : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype row] {q : ℕ} {exponent : κ → (Fin 1 →₀ ℕ)} (hexp : Function.Injective exponent)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q 1 z exponent
          (fun p => ![Complex.exp] p.2 (z p.1))).mulVec :=
  exists_row_packet_upperHalfPlane_of_algebraicIndependent
    algebraicIndependent_restrict_jetEvaluationFamily_exp hexp f hf

end GaloisForLFunctions.HTGeometry
