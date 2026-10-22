import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompactifiedPhaseProfile

/-!
# Fixed-lattice jets do not determine an arbitrary order isomorphism

Fixed-lattice rigidity says that two Suzuki carriers agreeing in value and first derivative at
every even phase lattice point are equal.  That statement is *false* for an arbitrary order
isomorphism of the line, and this module proves it false by exhibiting a counterexample.

The obstruction is the wobble `x + (1 - cos x) / 2`.  It fixes every point of `2 pi ZZ`, because
the cosine equals one there, and it has derivative one at every such point, because the sine
vanishes there.  Composing a carrier with it therefore changes nothing the lattice jets can see,
while changing the carrier.

Consequently the rigidity theorem is a statement about the *analytic* Suzuki carrier class — where
the Donoghue measure reconstructs the Herglotz function and hence the phase — and not about the
order-isomorphism model alone.  Any Lean proof of it must carry that analytic structure as a
hypothesis; no argument phrased on `ℝ ≃o ℝ` can succeed.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- A wobble of the line fixing the even phase lattice to first order. -/
noncomputable def latticeWobble (x : ℝ) : ℝ := x + (1 - Real.cos x) / 2

theorem hasDerivAt_latticeWobble (x : ℝ) :
    HasDerivAt latticeWobble (1 + Real.sin x / 2) x := by
  have hc : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have h : HasDerivAt (fun z : ℝ => z + (1 - Real.cos z) / 2)
      ((1 : ℝ) + (0 - -Real.sin x) / 2) x :=
    (hasDerivAt_id x).add (((hasDerivAt_const x (1 : ℝ)).sub hc).div_const 2)
  have hval : (1 : ℝ) + (0 - -Real.sin x) / 2 = 1 + Real.sin x / 2 := by ring
  rw [hval] at h
  exact h

theorem deriv_latticeWobble (x : ℝ) : deriv latticeWobble x = 1 + Real.sin x / 2 :=
  (hasDerivAt_latticeWobble x).deriv

theorem strictMono_latticeWobble : StrictMono latticeWobble := by
  refine strictMono_of_deriv_pos ?_
  intro x
  rw [deriv_latticeWobble]
  have := Real.neg_one_le_sin x
  linarith

theorem continuous_latticeWobble : Continuous latticeWobble :=
  continuous_id.add ((continuous_const.sub Real.continuous_cos).div_const 2)

theorem latticeWobble_ge (x : ℝ) : x ≤ latticeWobble x := by
  have := Real.cos_le_one x
  rw [latticeWobble]
  linarith

theorem latticeWobble_le (x : ℝ) : latticeWobble x ≤ x + 1 := by
  have := Real.neg_one_le_cos x
  rw [latticeWobble]
  linarith

theorem tendsto_latticeWobble_atTop : Tendsto latticeWobble atTop atTop :=
  tendsto_atTop_mono latticeWobble_ge tendsto_id

theorem tendsto_latticeWobble_atBot : Tendsto latticeWobble atBot atBot := by
  refine tendsto_atBot_mono latticeWobble_le ?_
  exact Filter.tendsto_atBot_add_const_right _ 1 Filter.tendsto_id

theorem surjective_latticeWobble : Function.Surjective latticeWobble :=
  continuous_latticeWobble.surjective tendsto_latticeWobble_atTop tendsto_latticeWobble_atBot

/-- The wobble as an order isomorphism of the line. -/
noncomputable def latticeWobbleIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective latticeWobble strictMono_latticeWobble surjective_latticeWobble

@[simp] theorem coe_latticeWobbleIso (x : ℝ) : latticeWobbleIso x = latticeWobble x := rfl

/-- The wobble fixes every point of the doubled lattice, because the cosine is one there. -/
theorem latticeWobble_int_mul_two_pi (k : ℤ) :
    latticeWobble ((k : ℝ) * (2 * Real.pi)) = (k : ℝ) * (2 * Real.pi) := by
  rw [latticeWobble, Real.cos_int_mul_two_pi]
  ring

theorem sin_int_mul_two_pi (k : ℤ) : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
  have hcast : (k : ℝ) * (2 * Real.pi) = ((2 * k : ℤ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hcast, Real.sin_int_mul_pi]

theorem pi_add_evenPhaseLattice (k : ℤ) :
    Real.pi + suzukiEvenPhaseLattice k = (k : ℝ) * (2 * Real.pi) := by
  rw [suzukiEvenPhaseLattice]
  ring

/-- **Fixed-lattice jets do not determine an order isomorphism.**  Two carriers can agree in value
and in first derivative at every even phase lattice point and still differ.  The rigidity theorem
therefore needs the analytic carrier class, not merely the order structure. -/
theorem not_fixedLatticeJets_determine_carrier :
    ∃ φ₁ φ₂ : ℝ ≃o ℝ, φ₁ ≠ φ₂ ∧
      (∀ k : ℤ, suzukiCompactifiedInversePhase φ₁ (suzukiEvenPhaseLattice k)
          = suzukiCompactifiedInversePhase φ₂ (suzukiEvenPhaseLattice k)) ∧
      (∀ k : ℤ, ∃ v : ℝ,
        HasDerivAt (suzukiCompactifiedInversePhase φ₁) v (suzukiEvenPhaseLattice k) ∧
        HasDerivAt (suzukiCompactifiedInversePhase φ₂) v (suzukiEvenPhaseLattice k)) := by
  refine ⟨OrderIso.refl ℝ, latticeWobbleIso.symm, ?_, ?_, ?_⟩
  · -- the two carriers differ, since the wobble moves `pi`
    intro h
    have h1 : (latticeWobbleIso.symm : ℝ → ℝ) Real.pi = Real.pi := by
      rw [← h]
      rfl
    have h3 : Real.pi = latticeWobble Real.pi := by
      have hc := congrArg (fun x : ℝ => (latticeWobbleIso : ℝ → ℝ) x) h1
      simp only [OrderIso.apply_symm_apply, coe_latticeWobbleIso] at hc
      exact hc
    rw [latticeWobble, Real.cos_pi] at h3
    linarith
  · -- equal values at every lattice point
    intro k
    have hfun1 : suzukiCompactifiedInversePhase (OrderIso.refl ℝ) (suzukiEvenPhaseLattice k)
        = Real.arctan (Real.pi + suzukiEvenPhaseLattice k) := rfl
    have hfun2 : suzukiCompactifiedInversePhase latticeWobbleIso.symm (suzukiEvenPhaseLattice k)
        = Real.arctan (latticeWobble (Real.pi + suzukiEvenPhaseLattice k)) := rfl
    rw [hfun1, hfun2, pi_add_evenPhaseLattice, latticeWobble_int_mul_two_pi]
  · -- equal first derivatives at every lattice point
    intro k
    have hpt := pi_add_evenPhaseLattice k
    have hadd : HasDerivAt (fun y : ℝ => Real.pi + y) 1 (suzukiEvenPhaseLattice k) :=
      HasDerivAt.const_add Real.pi (hasDerivAt_id (suzukiEvenPhaseLattice k))
    refine ⟨1 / (1 + ((k : ℝ) * (2 * Real.pi)) ^ (2 : ℕ)) * 1, ?_, ?_⟩
    · have h := hadd.arctan
      rw [hpt] at h
      exact h
    · have hcomp : HasDerivAt (fun y : ℝ => latticeWobble (Real.pi + y))
          ((1 + Real.sin (Real.pi + suzukiEvenPhaseLattice k) / 2) * 1)
          (suzukiEvenPhaseLattice k) :=
        (hasDerivAt_latticeWobble _).comp _ hadd
      have h := hcomp.arctan
      rw [hpt, latticeWobble_int_mul_two_pi, sin_int_mul_two_pi] at h
      have hval : 1 / (1 + ((k : ℝ) * (2 * Real.pi)) ^ (2 : ℕ)) * ((1 + 0 / 2) * 1)
          = 1 / (1 + ((k : ℝ) * (2 * Real.pi)) ^ (2 : ℕ)) * 1 := by ring
      rw [hval] at h
      exact h

/-! ## The refutation survives the Suzuki reflection normalization

A genuine Suzuki carrier obeys the reflection normalization `φ (-x) = 2 π - φ x`, which the two
carriers above do not.  The refutation is not an artefact of that: replacing the wobble by an *odd*
one, `x + sin x (1 + cos x) / 4`, keeps both carriers inside the normalized class.  It fixes every
*odd* multiple of `pi` — which is exactly the even phase lattice — because the sine vanishes there,
and its derivative there is one because `1 + cos` vanishes there too. -/

/-- An odd wobble fixing every odd multiple of `pi` to first order. -/
noncomputable def oddWobble (x : ℝ) : ℝ := x + Real.sin x * (1 + Real.cos x) / 4

theorem oddWobble_neg (x : ℝ) : oddWobble (-x) = -oddWobble x := by
  rw [oddWobble, oddWobble, Real.sin_neg, Real.cos_neg]
  ring

theorem hasDerivAt_oddWobble (x : ℝ) :
    HasDerivAt oddWobble
      (1 + (Real.cos x * (1 + Real.cos x) + Real.sin x * (0 + -Real.sin x)) / 4) x :=
  (hasDerivAt_id x).add
    (((Real.hasDerivAt_sin x).mul ((hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_cos x))).div_const 4)

theorem deriv_oddWobble (x : ℝ) :
    deriv oddWobble x
      = 1 + (Real.cos x * (1 + Real.cos x) + Real.sin x * (0 + -Real.sin x)) / 4 :=
  (hasDerivAt_oddWobble x).deriv

theorem strictMono_oddWobble : StrictMono oddWobble := by
  refine strictMono_of_deriv_pos ?_
  intro x
  rw [deriv_oddWobble]
  have hpyth : Real.sin x ^ (2 : ℕ) + Real.cos x ^ (2 : ℕ) = 1 := Real.sin_sq_add_cos_sq x
  nlinarith [hpyth, Real.neg_one_le_cos x, Real.cos_le_one x, sq_nonneg (Real.cos x + 1 / 4)]

theorem oddWobble_ge (x : ℝ) : x - 1 / 2 ≤ oddWobble x := by
  rw [oddWobble]
  nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x, Real.neg_one_le_cos x, Real.cos_le_one x]

theorem oddWobble_le (x : ℝ) : oddWobble x ≤ x + 1 / 2 := by
  rw [oddWobble]
  nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x, Real.neg_one_le_cos x, Real.cos_le_one x]

theorem continuous_oddWobble : Continuous oddWobble :=
  continuous_id.add ((Real.continuous_sin.mul (continuous_const.add Real.continuous_cos)).div_const 4)

theorem surjective_oddWobble : Function.Surjective oddWobble := by
  refine continuous_oddWobble.surjective ?_ ?_
  · exact tendsto_atTop_mono oddWobble_ge (Filter.tendsto_atTop_add_const_right _ (-(1 / 2))
      Filter.tendsto_id)
  · exact tendsto_atBot_mono oddWobble_le (Filter.tendsto_atBot_add_const_right _ (1 / 2)
      Filter.tendsto_id)

/-- The even phase lattice consists of odd multiples of `pi`. -/
theorem evenPhaseLattice_eq_int_mul_pi (k : ℤ) :
    suzukiEvenPhaseLattice k = ((2 * k - 1 : ℤ) : ℝ) * Real.pi := by
  rw [suzukiEvenPhaseLattice]
  push_cast
  ring

theorem sin_evenPhaseLattice (k : ℤ) : Real.sin (suzukiEvenPhaseLattice k) = 0 := by
  rw [evenPhaseLattice_eq_int_mul_pi, Real.sin_int_mul_pi]

theorem cos_evenPhaseLattice (k : ℤ) : Real.cos (suzukiEvenPhaseLattice k) = -1 := by
  have hrw : suzukiEvenPhaseLattice k = (k : ℝ) * (2 * Real.pi) - Real.pi := by
    rw [suzukiEvenPhaseLattice]
    ring
  rw [hrw, Real.cos_sub, Real.cos_int_mul_two_pi, sin_int_mul_two_pi, Real.cos_pi, Real.sin_pi]
  ring

theorem oddWobble_evenPhaseLattice (k : ℤ) :
    oddWobble (suzukiEvenPhaseLattice k) = suzukiEvenPhaseLattice k := by
  rw [oddWobble, sin_evenPhaseLattice]
  ring

/-- The wobble as an order isomorphism, shifted so that it acts on the centered coordinate. -/
noncomputable def shiftedOddWobble (z : ℝ) : ℝ := oddWobble (z - Real.pi)

theorem strictMono_shiftedOddWobble : StrictMono shiftedOddWobble :=
  fun _ _ hab => strictMono_oddWobble (by linarith)

theorem surjective_shiftedOddWobble : Function.Surjective shiftedOddWobble := by
  intro y
  obtain ⟨x, hx⟩ := surjective_oddWobble y
  exact ⟨x + Real.pi, by rw [shiftedOddWobble, add_sub_cancel_right, hx]⟩

noncomputable def shiftedOddWobbleIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective shiftedOddWobble strictMono_shiftedOddWobble
    surjective_shiftedOddWobble

@[simp] theorem coe_shiftedOddWobbleIso (z : ℝ) :
    shiftedOddWobbleIso z = oddWobble (z - Real.pi) := rfl

/-- The plain shift, giving the reference carrier. -/
noncomputable def shiftedIdentity (z : ℝ) : ℝ := z - Real.pi

theorem strictMono_shiftedIdentity : StrictMono shiftedIdentity :=
  fun _ _ hab => by simpa [shiftedIdentity] using hab

theorem surjective_shiftedIdentity : Function.Surjective shiftedIdentity :=
  fun y => ⟨y + Real.pi, by simp [shiftedIdentity]⟩

noncomputable def shiftedIdentityIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective shiftedIdentity strictMono_shiftedIdentity
    surjective_shiftedIdentity

@[simp] theorem coe_shiftedIdentityIso (z : ℝ) : shiftedIdentityIso z = z - Real.pi := rfl

/-- A carrier obeys the Suzuki reflection normalization as soon as its inverse anticommutes with
the reflection about `pi`. -/
theorem orderIso_symm_reflection {G : ℝ ≃o ℝ}
    (hg : ∀ u, G (2 * Real.pi - u) = -G u) (x : ℝ) :
    G.symm (-x) = 2 * Real.pi - G.symm x := by
  have h1 : G (2 * Real.pi - G.symm x) = -x := by
    rw [hg, G.apply_symm_apply]
  calc G.symm (-x) = G.symm (G (2 * Real.pi - G.symm x)) := by rw [h1]
    _ = 2 * Real.pi - G.symm x := G.symm_apply_apply _

/-- **The refutation inside the normalized class.**  Two carriers both obeying the Suzuki
reflection normalization can agree in value and in first derivative at every even phase lattice
point and still differ.  So fixed-lattice rigidity fails even after normalization: it is not the
order structure but the analytic structure that carries the theorem. -/
theorem not_fixedLatticeJets_determine_reflectionNormalized_carrier :
    ∃ φ₁ φ₂ : ℝ ≃o ℝ,
      (∀ x, φ₁ (-x) = 2 * Real.pi - φ₁ x) ∧
      (∀ x, φ₂ (-x) = 2 * Real.pi - φ₂ x) ∧
      φ₁ ≠ φ₂ ∧
      (∀ k : ℤ, suzukiCompactifiedInversePhase φ₁ (suzukiEvenPhaseLattice k)
          = suzukiCompactifiedInversePhase φ₂ (suzukiEvenPhaseLattice k)) ∧
      (∀ k : ℤ, ∃ v : ℝ,
        HasDerivAt (suzukiCompactifiedInversePhase φ₁) v (suzukiEvenPhaseLattice k) ∧
        HasDerivAt (suzukiCompactifiedInversePhase φ₂) v (suzukiEvenPhaseLattice k)) := by
  refine ⟨shiftedIdentityIso.symm, shiftedOddWobbleIso.symm, ?_, ?_, ?_, ?_, ?_⟩
  · refine orderIso_symm_reflection ?_
    intro u
    simp only [coe_shiftedIdentityIso]
    ring
  · refine orderIso_symm_reflection ?_
    intro u
    simp only [coe_shiftedOddWobbleIso]
    have harg : 2 * Real.pi - u - Real.pi = -(u - Real.pi) := by ring
    rw [harg, oddWobble_neg]
  · -- the carriers differ, since the odd wobble moves `pi / 2`
    intro h
    have h2 : shiftedIdentityIso = shiftedOddWobbleIso := by
      have := congrArg OrderIso.symm h
      rwa [OrderIso.symm_symm, OrderIso.symm_symm] at this
    have h3 : shiftedIdentityIso (Real.pi + Real.pi / 2)
        = shiftedOddWobbleIso (Real.pi + Real.pi / 2) := by rw [h2]
    simp only [coe_shiftedIdentityIso, coe_shiftedOddWobbleIso, add_sub_cancel_left,
      oddWobble, Real.sin_pi_div_two, Real.cos_pi_div_two] at h3
    linarith
  · -- equal values at every lattice point
    intro k
    have hfun1 : suzukiCompactifiedInversePhase shiftedIdentityIso.symm
        (suzukiEvenPhaseLattice k) = Real.arctan (Real.pi + suzukiEvenPhaseLattice k - Real.pi) :=
      rfl
    have hfun2 : suzukiCompactifiedInversePhase shiftedOddWobbleIso.symm
        (suzukiEvenPhaseLattice k)
        = Real.arctan (oddWobble (Real.pi + suzukiEvenPhaseLattice k - Real.pi)) := rfl
    rw [hfun1, hfun2, add_sub_cancel_left, oddWobble_evenPhaseLattice]
  · -- equal first derivatives at every lattice point
    intro k
    have hid : HasDerivAt (fun y : ℝ => Real.pi + y - Real.pi) 1 (suzukiEvenPhaseLattice k) := by
      have h := HasDerivAt.const_add Real.pi (hasDerivAt_id (suzukiEvenPhaseLattice k))
      simpa using h.sub_const Real.pi
    refine ⟨1 / (1 + suzukiEvenPhaseLattice k ^ (2 : ℕ)) * 1, ?_, ?_⟩
    · have h := hid.arctan
      rw [add_sub_cancel_left] at h
      exact h
    · have hcomp : HasDerivAt (fun y : ℝ => oddWobble (Real.pi + y - Real.pi))
          ((1 + (Real.cos (Real.pi + suzukiEvenPhaseLattice k - Real.pi)
              * (1 + Real.cos (Real.pi + suzukiEvenPhaseLattice k - Real.pi))
            + Real.sin (Real.pi + suzukiEvenPhaseLattice k - Real.pi)
              * (0 + -Real.sin (Real.pi + suzukiEvenPhaseLattice k - Real.pi))) / 4) * 1)
          (suzukiEvenPhaseLattice k) :=
        (hasDerivAt_oddWobble _).comp _ hid
      have h := hcomp.arctan
      rw [add_sub_cancel_left, oddWobble_evenPhaseLattice, sin_evenPhaseLattice,
        cos_evenPhaseLattice] at h
      have hval : 1 / (1 + suzukiEvenPhaseLattice k ^ (2 : ℕ))
            * ((1 + (-1 * (1 + -1) + 0 * (0 + -0)) / 4) * 1)
          = 1 / (1 + suzukiEvenPhaseLattice k ^ (2 : ℕ)) * 1 := by ring
      rw [hval] at h
      exact h

end GaloisForLFunctions.RHTower
