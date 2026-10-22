import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWFullNativeAdjointSymmetrizer

/-!
# PW-B cross-mode intertwiner obstruction

The physical full/native source vertex is an eigenvector of the triangular
mode action at the angular eigenvalue `mu`. An adjoint-compatible map may mix
angular modes, but its full dual component has eigenvalue `lam`, independent
of the destination mode. Since the actual Xi-labelled `lam` is nonreal and
angular eigenvalues are real, every compatible cross-mode block loses full
source contact. A block between distinct angular eigenvalues annihilates the
entire source vertex. Finite sums of such blocks cannot recover full contact.

The same-mode native dual component survives. This excludes regular,
adjoint-compatible finite spectral mixing, not singular spectral maps or
nonconserved anomaly currents; no RH or optical incidence is asserted.
-/

namespace RHTower.D4BMPWFullNativeAdjointSymmetrizer
open D4BMModularCore D4BMGlobalAngularResponse

noncomputable section
set_option autoImplicit false

/-- An arbitrary compatible source-to-target mode block loses its full dual
contact whenever source angular eigenvalue differs from full coupling. -/
theorem cross_mode_source_full_dual_zero
    (lam mu nu a b c d H Q : ℂ)
    (hmu : mu ≠ lam)
    (hcompat : ∀ p : ℂ × ℂ,
      arbitraryModeMap a b c d (modeAction lam mu p) =
        modeAdjointAction lam nu (arbitraryModeMap a b c d p))
    (hsource : mu * H = lam * (H + Q)) :
    (arbitraryModeMap a b c d (H, Q)).1 = 0 := by
  have h := congrArg Prod.fst (hcompat (H, Q))
  dsimp [arbitraryModeMap, modeAction, modeAdjointAction] at h
  have hz : (mu - lam) * (a * H + b * Q) = 0 := by
    linear_combination h + a * hsource
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hmu)

/-- Off-diagonal angular mixing annihilates the whole physical source vertex;
only a same-eigenvalue native-channel output can survive. -/
theorem cross_mode_source_zero_of_distinct
    (lam mu nu a b c d H Q : ℂ)
    (hmu : mu ≠ lam) (hnu : mu ≠ nu)
    (hcompat : ∀ p : ℂ × ℂ,
      arbitraryModeMap a b c d (modeAction lam mu p) =
        modeAdjointAction lam nu (arbitraryModeMap a b c d p))
    (hsource : mu * H = lam * (H + Q)) :
    arbitraryModeMap a b c d (H, Q) = (0, 0) := by
  have hfirst := cross_mode_source_full_dual_zero lam mu nu a b c d H Q
    hmu hcompat hsource
  dsimp [arbitraryModeMap] at hfirst
  have h := congrArg Prod.snd (hcompat (H, Q))
  dsimp [arbitraryModeMap, modeAction, modeAdjointAction] at h
  have hz : (mu - nu) * (c * H + d * Q) = 0 := by
    linear_combination h + c * hsource + lam * hfirst
  have hsecond : (arbitraryModeMap a b c d (H, Q)).2 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hnu)
  exact Prod.ext hfirst hsecond

/-- Every finite matrix of compatible mode blocks has zero full source
contact, regardless of how widely it mixes destination modes. -/
theorem finite_cross_mode_source_full_contact_zero
    {ι κ : Type*} [Fintype ι]
    (lam : ℂ) (mu : ι → ℂ) (nu : κ → ℂ)
    (a b c d : κ → ι → ℂ) (H Q : ι → ℂ)
    (hmu : ∀ i, mu i ≠ lam)
    (hcompat : ∀ (j : κ) (i : ι) (p : ℂ × ℂ),
      arbitraryModeMap (a j i) (b j i) (c j i) (d j i)
        (modeAction lam (mu i) p) =
      modeAdjointAction lam (nu j)
        (arbitraryModeMap (a j i) (b j i) (c j i) (d j i) p))
    (hsource : ∀ i, mu i * H i = lam * (H i + Q i))
    (j : κ) :
    (∑ i : ι,
      (arbitraryModeMap (a j i) (b j i) (c j i) (d j i) (H i, Q i)).1) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact cross_mode_source_full_dual_zero lam (mu i) (nu j)
    (a j i) (b j i) (c j i) (d j i) (H i) (Q i)
    (hmu i) (hcompat j i) (hsource i)

private theorem physical_parameter_not_real_mode
    (q : XiZeroCopy) (branch : Bool) (mu : ℝ) :
    (mu : ℂ) ≠ parameter q branch := by
  have hnonreal : (parameter q branch).im ≠ 0 := by
    cases branch
    · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).2
    · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).1
  intro h
  have hz : (parameter q branch).im = 0 := by
    have hi := congrArg Complex.im h
    simpa using hi.symm
  exact hnonreal hz

/-- No finite, adjoint-compatible mixing of real angular modes transports the
actual Xi-labelled source vertex into a full dual contact. -/
theorem physical_finite_cross_mode_full_contact_zero
    {ι κ : Type*} [Fintype ι]
    (q : XiZeroCopy) (branch : Bool)
    (mu : ι → ℝ) (nu : κ → ℝ)
    (a b c d : κ → ι → ℂ) (H Q : ι → ℂ)
    (hcompat : ∀ (j : κ) (i : ι) (p : ℂ × ℂ),
      arbitraryModeMap (a j i) (b j i) (c j i) (d j i)
        (modeAction (parameter q branch) (mu i) p) =
      modeAdjointAction (parameter q branch) (nu j)
        (arbitraryModeMap (a j i) (b j i) (c j i) (d j i) p))
    (hsource : ∀ i, (mu i : ℂ) * H i =
      parameter q branch * (H i + Q i))
    (j : κ) :
    (∑ i : ι,
      (arbitraryModeMap (a j i) (b j i) (c j i) (d j i) (H i, Q i)).1) = 0 := by
  exact finite_cross_mode_source_full_contact_zero
    (parameter q branch) (fun i => (mu i : ℂ)) (fun j => (nu j : ℂ))
    a b c d H Q
    (fun i => physical_parameter_not_real_mode q branch (mu i))
    hcompat hsource j

end
end RHTower.D4BMPWFullNativeAdjointSymmetrizer
