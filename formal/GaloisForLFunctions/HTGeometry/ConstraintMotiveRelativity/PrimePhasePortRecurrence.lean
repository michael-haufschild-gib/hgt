import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationCompletion
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimePortCapacityHierarchy
import GaloisForLFunctions.HTGeometry.EulerPrimeOrbitFourOrganLaw

/-!
# The arithmetic phase port: recurrence and completion

The prime-log Mellin clock turns the augmentation into the family of ports
`ε_t x = ∑ p^{-it} x_p`.  Each `ε_t` is the port of the unimodular covector `λ_t = (p^{-it})`, so
the whole algebraic and completion theory of a unimodular port applies verbatim at every time:
the algebraic reduction is one hyperbolic port, `ℓ¹` retains it, and `ℓ^p` for `p > 1` and `c₀`
erase it.  The separation loss is therefore uniform in time.

On the observation side the same orbit is recurrent at every finite aperture and has constant sup
norm one, while its logarithmic lift has unbounded squared length, and while every finite jet
system is a basis of the finite cotangent space, the infinite orbit has no derivative in the
unweighted continuous dual: the generator lives only in a weighted predual.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open scoped BigOperators

section PhasePort

/-- **`(PR.1)`.**  The arithmetic phase covector `λ_t = (p^{-it})`. -/
noncomputable def phaseCovec (t : ℝ) (p : Nat.Primes) : ℂ :=
  portCoef primeLog (fun _ => 1) t p

theorem phaseCovec_eq (t : ℝ) (p : Nat.Primes) :
    phaseCovec t p = Complex.exp (-(Complex.I * ((t * Real.log (p : ℕ) : ℝ) : ℂ))) := by
  rw [phaseCovec, portCoef, one_mul, portPhase, primeLog]

@[simp] theorem norm_phaseCovec (t : ℝ) (p : Nat.Primes) : ‖phaseCovec t p‖ = 1 := by
  rw [phaseCovec, norm_portCoef, norm_one]

theorem phaseCovec_ne_zero (t : ℝ) (p : Nat.Primes) : phaseCovec t p ≠ 0 := by
  intro h
  have := norm_phaseCovec t p
  rw [h, norm_zero] at this
  exact zero_ne_one this

@[simp] theorem phaseCovec_zero (p : Nat.Primes) : phaseCovec 0 p = 1 := by
  rw [phaseCovec, portCoef, portPhase_zero, mul_one]

/-- The phase covector written as the arithmetic power `p^{-it}`. -/
theorem phaseCovec_eq_cpow (t : ℝ) (p : Nat.Primes) :
    phaseCovec t p = (((p : ℕ) : ℂ)) ^ (-(t : ℂ) * Complex.I) := by
  have hne : (((p : ℕ) : ℂ)) ≠ 0 := by
    have : 0 < (p : ℕ) := p.2.pos
    exact_mod_cast Nat.cast_ne_zero.2 this.ne'
  rw [phaseCovec_eq, Complex.cpow_def_of_ne_zero hne, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-! ### Theorem 1 — the algebraic recurrent port -/

/-- **`(PR.2)`.**  The annihilator of the time-`t` constraint is the line of `λ_t`. -/
theorem dualAnnihilator_phaseIdeal (t : ℝ) :
    (wtIdeal (phaseCovec t)).dualAnnihilator
      = Submodule.span ℂ {(wtPort (phaseCovec t) : Module.Dual ℂ (Nat.Primes →₀ ℂ))} :=
  dualAnnihilator_wtIdeal (phaseCovec_ne_zero t)

/-- **`(PR.2)`.**  The time-`t` coisotropic quotient is the hyperbolic plane. -/
theorem phase_coisotropic_reduction (t : ℝ) (p₀ : Nat.Primes) :
    (∀ z : ℂ × ℂ, ∃ u ∈ portOrth (wtIsotropic (phaseCovec t)),
        wtRed (phaseCovec t) p₀ u = z) ∧
    portOrth (wtIsotropic (phaseCovec t)) ⊓ LinearMap.ker (wtRed (phaseCovec t) p₀)
      = wtIsotropic (phaseCovec t) ∧
    (∀ u ∈ portOrth (wtIsotropic (phaseCovec t)), ∀ v ∈ portOrth (wtIsotropic (phaseCovec t)),
      portForm u v = hyperbolicForm (wtRed (phaseCovec t) p₀ u) (wtRed (phaseCovec t) p₀ v)) :=
  coisotropic_reduction_wt (phaseCovec_ne_zero t) p₀

theorem phaseIdeal_quotient_equiv (t : ℝ) :
    Nonempty ((((Nat.Primes →₀ ℂ) ⧸
      (wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)))) ≃ₗ[ℂ] ℂ) :=
  wtIdeal_quotient_equiv (phaseCovec_ne_zero t)

/-! ### `(PR.3)` — the finite phase orbit is dense and recurrent -/

/-- **`(PR.3)`, density.**  Every prescribed phase vector on a finite prime aperture is approximated
by the orbit.  Unique factorization makes the coordinate log-frequencies rationally independent, so
Kronecker's theorem applies. -/
theorem phase_orbit_approx (F : Finset Nat.Primes) (θ : F → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∀ p : F, ‖phaseCovec t p - Complex.exp ((θ p : ℝ) * Complex.I)‖ < ε := by
  classical
  obtain ⟨t, ht⟩ :=
    _root_.GaloisForLFunctions.HTGeometry.finiteDiagonalPhaseOrbit_approx
      (frequency := fun p : F => Real.log ((p : Nat.Primes) : ℕ))
      (_root_.GaloisForLFunctions.primeLogFiniteSlice_linearIndependent F)
      (weight := fun _ : F => (1 : ℂ)) (fun _ => one_ne_zero) θ hε
  refine ⟨t, fun p => ?_⟩
  have hp := ht p
  simp only [_root_.GaloisForLFunctions.HTGeometry.finiteDiagonalPhaseOrbit, one_mul,
    norm_one] at hp
  have hrw : phaseCovec t (p : Nat.Primes)
      = _root_.GaloisForLFunctions.expChar (-Real.log ((p : Nat.Primes) : ℕ)) t := by
    rw [phaseCovec_eq, _root_.GaloisForLFunctions.expChar]
    congr 1
    push_cast
    ring
  rw [hrw]
  simpa using hp

/-- **`(PR.3)`, recurrence.**  At arbitrarily late times the finite phase orbit returns to within
`ε` of its start. -/
theorem phase_orbit_recurrent (F : Finset Nat.Primes) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, T < t ∧ ∀ p : F, ‖phaseCovec t p - 1‖ < ε := by
  classical
  have hsum : Summable fun _ : F => ‖(1 : ℂ)‖ ^ 2 := Summable.of_finite
  obtain ⟨t, hT, hlt⟩ :=
    portOrbit_recurrent (θ := fun p : F => Real.log ((p : Nat.Primes) : ℕ))
      (c := fun _ : F => (1 : ℂ)) (h := hsum) hε T
  refine ⟨t, hT, fun p => ?_⟩
  have hcoord := lp.norm_apply_le_norm (E := fun _ : F => ℂ) (by norm_num)
    (portOrbit (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) (fun _ : F => (1 : ℂ)) hsum t
      - portOrbit (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) (fun _ : F => (1 : ℂ)) hsum 0) p
  rw [lp.coeFn_sub] at hcoord
  simp only [Pi.sub_apply, portOrbit_apply, portCoef_zero] at hcoord
  have hval : portCoef (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) (fun _ : F => (1 : ℂ)) t p
      = phaseCovec t (p : Nat.Primes) := by
    rw [portCoef, one_mul, phaseCovec, portCoef, one_mul, portPhase, portPhase, primeLog]
  rw [hval] at hcoord
  calc ‖phaseCovec t (p : Nat.Primes) - 1‖ ≤ _ := hcoord
    _ < ε := hlt

end PhasePort

section PhaseCompletion

/-! ### Theorems 2 and 3 — the completion phase is uniform in time -/

/-- **Theorem 2.**  The time-`t` port extends continuously to `ℓ¹`. -/
noncomputable def phaseCLM (t : ℝ) : lp (fun _ : Nat.Primes => ℂ) 1 →L[ℂ] ℂ :=
  wtCLM (phaseCovec t) (norm_phaseCovec t)

/-- **`(PR.4)`.**  In `ℓ¹` the closure of the time-`t` constraint is the kernel of the extended
port, and that kernel has codimension one with annihilator the line of the port. -/
theorem closure_image_phaseIdeal_one (t : ℝ) :
    closure ((lpEmb Nat.Primes 1) ''
        ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ)))
      = {x : lp (fun _ : Nat.Primes => ℂ) 1 | phaseCLM t x = 0} :=
  closure_image_wtIdeal_one (phaseCovec_ne_zero t) (norm_phaseCovec t)

theorem phaseCLM_surjective (t : ℝ) : Function.Surjective (phaseCLM t) :=
  wtCLM_surjective (phaseCovec_ne_zero t) (norm_phaseCovec t)

theorem eq_smul_phaseCLM_of_vanishing (t : ℝ) (q₀ : Nat.Primes)
    (g : lp (fun _ : Nat.Primes => ℂ) 1 →L[ℂ] ℂ)
    (hg : ∀ x : lp (fun _ : Nat.Primes => ℂ) 1, phaseCLM t x = 0 → g x = 0) :
    ∀ x, g x = g (lp.single (1 : ENNReal) q₀ (phaseCovec t q₀)⁻¹) * phaseCLM t x :=
  eq_smul_wtCLM_of_vanishing (phaseCovec_ne_zero t) (norm_phaseCovec t) q₀ g hg

/-- **`(PR.5)`.**  In `ℓ^p` with `p > 1` the time-`t` constraint is dense. -/
theorem closure_image_phaseIdeal_lp (t : ℝ) {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p.toReal) :
    closure ((lpEmb Nat.Primes p) ''
        ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ)))
      = closure (Set.range (lpEmb Nat.Primes p)) :=
  closure_image_wtIdeal_lp (phaseCovec_ne_zero t) (norm_phaseCovec t) hp

/-- **`(PR.5)` for `c₀`.** -/
theorem closure_image_phaseIdeal_top (t : ℝ) :
    closure ((lpEmb Nat.Primes ⊤) ''
        ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ)))
      = closure (Set.range (lpEmb Nat.Primes ⊤)) :=
  closure_image_wtIdeal_top (phaseCovec_ne_zero t) (norm_phaseCovec t)

/-- **`(PR.5)`, the annihilator.**  In the erasing charts the time-`t` port has zero continuous
annihilator, so its Hausdorff reduction vanishes. -/
theorem phase_separation_defect_erasure (t : ℝ) {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p.toReal) :
    (∀ l : Nat.Primes →₀ ℂ, lpEmb Nat.Primes p l ∈ closure ((lpEmb Nat.Primes p) ''
        ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ)))) ∧
    (∀ g : lp (fun _ : Nat.Primes => ℂ) p →L[ℂ] ℂ,
        (∀ x, x ∈ closure ((lpEmb Nat.Primes p) ''
          ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ))) →
          g x = 0) → ∀ l : Nat.Primes →₀ ℂ, g (lpEmb Nat.Primes p l) = 0) :=
  separation_defect_erasure (phaseCovec t) (lpEmb Nat.Primes p)
    (fun ε hε => exists_small_spread_lp (phaseCovec_ne_zero t) (norm_phaseCovec t) hp ε hε)

/-- **`(PR.5)` for `c₀`, the annihilator.** -/
theorem phase_separation_defect_erasure_top (t : ℝ) :
    (∀ l : Nat.Primes →₀ ℂ, lpEmb Nat.Primes ⊤ l ∈ closure ((lpEmb Nat.Primes ⊤) ''
        ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ)))) ∧
    (∀ g : lp (fun _ : Nat.Primes => ℂ) ⊤ →L[ℂ] ℂ,
        (∀ x, x ∈ closure ((lpEmb Nat.Primes ⊤) ''
          ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ))) →
          g x = 0) → ∀ l : Nat.Primes →₀ ℂ, g (lpEmb Nat.Primes ⊤ l) = 0) :=
  separation_defect_erasure (phaseCovec t) (lpEmb Nat.Primes ⊤)
    (fun ε hε => exists_small_spread_top (phaseCovec_ne_zero t) (norm_phaseCovec t) ε hε)

/-- **`(PR.4)`, the `ℓ¹` defect vanishes at every time.** -/
theorem phase_separation_defect_one (t : ℝ) :
    (∀ l : Nat.Primes →₀ ℂ,
        lpEmb Nat.Primes 1 l ∈ closure ((lpEmb Nat.Primes 1) ''
          ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) : Set (Nat.Primes →₀ ℂ))) →
        wtPort (phaseCovec t) l = 0) ∧
    (∀ a : ℂ, ∃ g : lp (fun _ : Nat.Primes => ℂ) 1 →L[ℂ] ℂ,
        (∀ x : lp (fun _ : Nat.Primes => ℂ) 1,
          x ∈ closure ((lpEmb Nat.Primes 1) ''
            ((wtIdeal (phaseCovec t) : Submodule ℂ (Nat.Primes →₀ ℂ)) :
              Set (Nat.Primes →₀ ℂ))) → g x = 0) ∧
        ∀ l : Nat.Primes →₀ ℂ, g (lpEmb Nat.Primes 1 l) = a * wtPort (phaseCovec t) l) :=
  separation_defect_one (phaseCovec_ne_zero t) (norm_phaseCovec t)

end PhaseCompletion

section WeakStar

/-! ### Theorem 4 — the infinite recurrent observer -/

/-- **`(PR.7)`.**  The phase covector as a point of the unit torus inside `ℓ^∞`. -/
noncomputable def phaseVec (t : ℝ) : lp (fun _ : Nat.Primes => ℂ) ⊤ :=
  ⟨phaseCovec t, memℓp_infty ⟨1, by
    rintro y ⟨p, rfl⟩
    exact le_of_eq (norm_phaseCovec t p)⟩⟩

@[simp] theorem phaseVec_apply (t : ℝ) (p : Nat.Primes) :
    (phaseVec t : Nat.Primes → ℂ) p = phaseCovec t p := rfl

/-- **`(PR.10)`.**  The port norm is constantly one: it is phase-blind. -/
theorem norm_phaseVec (t : ℝ) : ‖phaseVec t‖ = 1 := by
  refine le_antisymm (lp.norm_le_of_forall_le (E := fun _ : Nat.Primes => ℂ) zero_le_one
    fun p => le_of_eq (norm_phaseCovec t p)) ?_
  have h2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have := lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (by norm_num) (phaseVec t) h2
  rwa [phaseVec_apply, norm_phaseCovec] at this

/-- **`(PR.9)`.**  The squared Euclidean length of the logarithmic lift on a finite aperture. -/
theorem phaseLiftEnergy_eq (F : Finset Nat.Primes) (t : ℝ) :
    _root_.GaloisForLFunctions.HTGeometry.finitePhaseLiftEnergy
        (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) t
      = t ^ 2 * ∑ p : F, Real.log ((p : Nat.Primes) : ℕ) ^ 2 := by
  rw [_root_.GaloisForLFunctions.HTGeometry.finitePhaseLiftEnergy, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **`(PR.8)`–`(PR.9)`.**  The lift length is unbounded on every nonempty aperture, while the
orbit itself recurs. -/
theorem phaseLiftEnergy_unbounded (F : Finset Nat.Primes) (hF : F.Nonempty) (R : ℝ) :
    ∃ t : ℝ, R < _root_.GaloisForLFunctions.HTGeometry.finitePhaseLiftEnergy
      (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) t := by
  obtain ⟨p₀, hp₀⟩ := hF
  letI : Nonempty F := ⟨⟨p₀, hp₀⟩⟩
  refine _root_.GaloisForLFunctions.HTGeometry.finitePhaseLiftEnergy_unbounded
    (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) ⟨p₀, hp₀⟩ ?_ R
  have : (1 : ℝ) < ((p₀ : ℕ) : ℝ) := by exact_mod_cast p₀.2.one_lt
  exact (Real.log_pos this).ne'

end WeakStar

section JetWall

/-! ### Theorem 5 — finite jet tomography and the generator wall -/

/-- The prime-log jet nodes are pairwise distinct. -/
theorem jetNode_injective :
    Function.Injective fun p : Nat.Primes => -(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ)) := by
  intro p q hpq
  refine _root_.GaloisForLFunctions.HTGeometry.eulerPrimeLogNode_injective ?_
  have h := hpq
  rw [neg_inj] at h
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact mul_left_cancel₀ hI h

/-- **`(PR.9a)`.**  On an aperture of `N` primes the first `N` time-jet covectors are linearly
independent, hence a basis of the finite cotangent space: the matrix `((-i log p)^n)` is a
Vandermonde matrix on distinct nodes. -/
theorem phaseJet_linearIndependent (F : Finset Nat.Primes) :
    LinearIndependent ℂ fun k : Fin (Fintype.card F) =>
      _root_.GaloisForLFunctions.HTGeometry.finiteDiagonalKrylovVector
        (fun p : F => -(Complex.I * ((Real.log ((p : Nat.Primes) : ℕ) : ℝ) : ℂ)))
        (fun _ : F => (1 : ℂ)) (k : ℕ) := by
  classical
  refine _root_.GaloisForLFunctions.HTGeometry.finiteDiagonalKrylovVector_linearIndependent
    ?_ (fun _ => one_ne_zero)
  exact jetNode_injective.comp Subtype.coe_injective

/-- **`(PR.9a)`, the invisible subspace.**  A fixed jet order `r` cannot see an aperture of more
than `r + 1` primes. -/
theorem phaseJet_span_ne_top (F : Finset Nat.Primes) (r : ℕ) (hr : r + 1 < Fintype.card F) :
    Submodule.span ℂ (Set.range fun k : Fin (r + 1) =>
        _root_.GaloisForLFunctions.HTGeometry.finiteDiagonalKrylovVector
          (fun p : F => -(Complex.I * ((Real.log ((p : Nat.Primes) : ℕ) : ℝ) : ℂ)))
          (fun _ : F => (1 : ℂ)) (k : ℕ)) ≠ ⊤ := by
  classical
  exact _root_.GaloisForLFunctions.HTGeometry.finiteDiagonalKrylov_span_ne_top_of_lt_card _ _ r hr

/-- The time derivative of a single phase coordinate. -/
theorem hasDerivAt_phaseCovec (t : ℝ) (p : Nat.Primes) :
    HasDerivAt (fun s : ℝ => phaseCovec s p)
      (-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ)) * phaseCovec t p) t := by
  have h := hasDerivAt_portCoef primeLog (fun _ : Nat.Primes => (1 : ℂ)) t p
  have hval : portCoef primeLog (jetCoef primeLog (fun _ : Nat.Primes => (1 : ℂ)) 1) t p
      = -(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ)) * phaseCovec t p := by
    rw [portCoef, jetCoef, pow_one, phaseCovec, portCoef, primeLog]
    ring
  rw [hval] at h
  exact h

/-- **Weak-star continuity.**  Pairing the orbit against a fixed `ℓ¹` vector is continuous in
time. -/
theorem continuous_weakStar_pairing (x : lp (fun _ : Nat.Primes => ℂ) 1) :
    Continuous fun t : ℝ => ∑' p : Nat.Primes, phaseCovec t p * (x : Nat.Primes → ℂ) p := by
  refine continuous_tsum (u := fun p => ‖(x : Nat.Primes → ℂ) p‖) ?_ (summable_norm_lp_one x) ?_
  · intro p
    have hc : Continuous fun t : ℝ => phaseCovec t p := by
      simpa [phaseCovec] using continuous_portCoef (θ := primeLog)
        (c := fun _ : Nat.Primes => (1 : ℂ)) p
    exact hc.mul continuous_const
  · intro p t
    rw [norm_mul, norm_phaseCovec, one_mul]

/-- **The generator wall.**  The orbit has no weak-star derivative at zero inside `ℓ^∞`: the
coordinate tests force the coefficient `-i log p`, which is unbounded. -/
theorem no_weakStar_derivative :
    ¬ ∃ v : lp (fun _ : Nat.Primes => ℂ) ⊤, ∀ p : Nat.Primes,
      HasDerivAt (fun s : ℝ => phaseCovec s p) ((v : Nat.Primes → ℂ) p) 0 := by
  rintro ⟨v, hv⟩
  obtain ⟨n, hn, hnp⟩ := Nat.exists_infinite_primes (Nat.ceil (Real.exp (‖v‖ + 1)) + 1)
  set p : Nat.Primes := ⟨n, hnp⟩ with hp
  have hcoord : (v : Nat.Primes → ℂ) p = -(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ)) := by
    have h1 := hv p
    have h2 := hasDerivAt_phaseCovec 0 p
    rw [phaseCovec_zero, mul_one] at h2
    exact h1.unique h2
  have hnorm : ‖(v : Nat.Primes → ℂ) p‖ = Real.log ((p : ℕ)) := by
    rw [hcoord, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    have h1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hnp.one_lt.le
    exact Real.log_nonneg h1
  have hle := lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (by norm_num) v p
  rw [hnorm] at hle
  have hbig : Real.exp (‖v‖ + 1) < ((p : ℕ) : ℝ) := by
    have h1 : Real.exp (‖v‖ + 1) ≤ (Nat.ceil (Real.exp (‖v‖ + 1)) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (‖v‖ + 1)) : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by
      have : Nat.ceil (Real.exp (‖v‖ + 1)) < (p : ℕ) := by
        have hpn : (p : ℕ) = n := rfl
        rw [hpn]
        omega
      exact_mod_cast this
    linarith
  have hlog : ‖v‖ + 1 < Real.log ((p : ℕ)) := by
    have hpos : (0 : ℝ) < Real.exp (‖v‖ + 1) := Real.exp_pos _
    have := Real.log_lt_log hpos hbig
    rwa [Real.log_exp] at this
  linarith

/-- **`(PR.9b)`.**  On the weighted predual `ℓ¹_{log^n}` the `n`-th jet coefficient functional is
bounded. -/
theorem weighted_predual_bound (n : ℕ) (x : Nat.Primes → ℂ)
    (hx : Summable fun p : Nat.Primes => ‖x p‖ * (1 + Real.log ((p : ℕ))) ^ n) :
    (Summable fun p : Nat.Primes =>
        (-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ))) ^ n * x p) ∧
      ‖∑' p : Nat.Primes, (-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ))) ^ n * x p‖
        ≤ ∑' p : Nat.Primes, ‖x p‖ * (1 + Real.log ((p : ℕ))) ^ n := by
  have hbound : ∀ p : Nat.Primes,
      ‖(-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ))) ^ n * x p‖
        ≤ ‖x p‖ * (1 + Real.log ((p : ℕ))) ^ n := by
    intro p
    have hlog : 0 ≤ Real.log ((p : ℕ)) := by
      have h1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
      exact Real.log_nonneg h1
    have hn1 : ‖(-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ))) ^ n‖
        = Real.log ((p : ℕ)) ^ n := by
      rw [norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog]
    rw [norm_mul, hn1, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (by linarith) n) (norm_nonneg _)
  have hsum : Summable fun p : Nat.Primes =>
      (-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ))) ^ n * x p :=
    Summable.of_norm_bounded hx hbound
  have hnormsum : Summable fun p : Nat.Primes =>
      ‖(-(Complex.I * ((Real.log ((p : ℕ)) : ℝ) : ℂ))) ^ n * x p‖ :=
    hx.of_nonneg_of_le (fun p => norm_nonneg _) hbound
  refine ⟨hsum, ?_⟩
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  exact hnormsum.tsum_le_tsum hbound hx

end JetWall

end HTGeometry.ConstraintMotiveRelativity
