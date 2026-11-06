import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy

/-!
# Pure compression and the missing invariant restriction

The canonical divisor symmetry pairs `ρ` with `1 - conj ρ`. In its even/odd orbit
coordinates, Frobenius has diagonal `1/2 + i Im ρ` and off-diagonal `Re ρ - 1/2`.
Thus the even compression is pure without any purity assumption on the divisor.
Preservation of the even subspace, however, is equivalent to the Riemann hypothesis.
-/

noncomputable section
open Complex
open RHTower

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

/-- The copy permutation underlying the canonical divisor monodromy. -/
def monodromyIndex (q : XiZeroCopy) : XiZeroCopy :=
  xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv q)

theorem monodromyIndex_involutive (q : XiZeroCopy) :
    monodromyIndex (monodromyIndex q) = q := by
  have hfst : (monodromyIndex (monodromyIndex q)).1 = q.1 := by
    apply Subtype.ext
    change deningerDivisorThetaEigen (monodromyIndex (monodromyIndex q)) =
      deningerDivisorThetaEigen q
    simp only [monodromyIndex, deningerDivisorThetaEigen_monodromy, map_sub, map_one,
      Complex.conj_conj]
    ring
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [monodromyIndex, xiZeroCopyConjEquiv, xiZeroCopyReflectEquiv,
    Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

theorem divisorMonodromy_involutive (x : DeningerDivisorH1) :
    deningerDivisorMonodromy (deningerDivisorMonodromy x) = x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add q c x _ _ ih =>
      rw [map_add, map_add, ih, deningerDivisorMonodromy_single,
        deningerDivisorMonodromy_single]
      rw [show xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv
        (xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv q))) = q from
          monodromyIndex_involutive q]

theorem divisorMonodromy_apply (x : DeningerDivisorH1) (q : XiZeroCopy) :
    deningerDivisorMonodromy x q = x (monodromyIndex q) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add r c x _ _ ih =>
      rw [map_add, Finsupp.add_apply, ih, deningerDivisorMonodromy_single,
        Finsupp.add_apply]
      congr 1
      change Finsupp.single (monodromyIndex r) c q = Finsupp.single r c (monodromyIndex q)
      have he : monodromyIndex r = q ↔ r = monodromyIndex q :=
        ⟨fun h => by rw [← h, monodromyIndex_involutive],
          fun h => by rw [h, monodromyIndex_involutive]⟩
      simp only [Finsupp.single_apply, he]

/-- Projection onto the fixed subspace of the canonical divisor monodromy. -/
def canonicalProjection : Module.End ℂ DeningerDivisorH1 :=
  (2 : ℂ)⁻¹ • (LinearMap.id + deningerDivisorMonodromy)

theorem canonicalProjection_apply (x : DeningerDivisorH1) :
    canonicalProjection x = (2 : ℂ)⁻¹ • (x + deningerDivisorMonodromy x) := rfl

theorem canonicalProjection_fixed (x : DeningerDivisorH1) :
    deningerDivisorMonodromy (canonicalProjection x) = canonicalProjection x := by
  rw [canonicalProjection_apply, map_smul, map_add, divisorMonodromy_involutive]
  rw [add_comm]

/-- Even and odd orbit vectors retain both members of a functional-equation pair. -/
def orbitEven (q : XiZeroCopy) : DeningerDivisorH1 :=
  Finsupp.single q 1 + Finsupp.single (monodromyIndex q) 1

def orbitOdd (q : XiZeroCopy) : DeningerDivisorH1 :=
  Finsupp.single q 1 - Finsupp.single (monodromyIndex q) 1

theorem orbitEven_ne_zero (q : XiZeroCopy) : orbitEven q ≠ 0 := by
  classical
  intro h
  have hv := congrArg (fun x : DeningerDivisorH1 => x q) h
  simp only [orbitEven, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply] at hv
  split_ifs at hv <;> norm_num at hv

/-- The diagonal of the orbit compression. -/
def orbitCenter (q : XiZeroCopy) : ℂ :=
  (deningerDivisorThetaEigen q + (1 - (starRingEnd ℂ) (deningerDivisorThetaEigen q))) / 2

/-- The coupling between even and odd orbit coordinates. -/
def orbitCoupling (q : XiZeroCopy) : ℂ :=
  (deningerDivisorThetaEigen q - (1 - (starRingEnd ℂ) (deningerDivisorThetaEigen q))) / 2

theorem orbitCenter_eq (q : XiZeroCopy) :
    orbitCenter q = 1 / 2 + (deningerDivisorThetaEigen q).im * I := by
  apply Complex.ext <;> simp [orbitCenter]

theorem orbitCoupling_eq (q : XiZeroCopy) :
    orbitCoupling q = ((deningerDivisorThetaEigen q).re - 1 / 2 : ℝ) := by
  apply Complex.ext
  · simp [orbitCoupling]
    ring
  · simp [orbitCoupling]

theorem monodromy_orbitEven (q : XiZeroCopy) :
    deningerDivisorMonodromy (orbitEven q) = orbitEven q := by
  simp only [orbitEven, map_add, deningerDivisorMonodromy_single]
  change Finsupp.single (monodromyIndex q) 1 +
    Finsupp.single (monodromyIndex (monodromyIndex q)) 1 = _
  rw [monodromyIndex_involutive, add_comm]

theorem monodromy_orbitOdd (q : XiZeroCopy) :
    deningerDivisorMonodromy (orbitOdd q) = -orbitOdd q := by
  simp only [orbitOdd, map_sub, deningerDivisorMonodromy_single]
  change Finsupp.single (monodromyIndex q) 1 -
    Finsupp.single (monodromyIndex (monodromyIndex q)) 1 = _
  rw [monodromyIndex_involutive, neg_sub]

/-- Frobenius on an even orbit vector has precisely the critical-line displacement as leakage. -/
theorem theta_orbitEven (q : XiZeroCopy) :
    deningerDivisorTheta (orbitEven q) =
      orbitCenter q • orbitEven q + orbitCoupling q • orbitOdd q := by
  classical
  ext p
  simp only [orbitEven, orbitOdd, map_add, deningerDivisorTheta_single,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, monodromyIndex, deningerDivisorThetaEigen_monodromy,
    orbitCenter, orbitCoupling]
  split_ifs <;> ring

/-- The complementary orbit vector carries the same diagonal and the same coupling. -/
theorem theta_orbitOdd (q : XiZeroCopy) :
    deningerDivisorTheta (orbitOdd q) =
      orbitCoupling q • orbitEven q + orbitCenter q • orbitOdd q := by
  classical
  ext p
  simp only [orbitEven, orbitOdd, map_sub, deningerDivisorTheta_single,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, monodromyIndex, deningerDivisorThetaEigen_monodromy,
    orbitCenter, orbitCoupling]
  split_ifs <;> ring

/-- The invariant compression has pure diagonal even when Frobenius leaves the invariant space. -/
theorem compressed_theta_orbitEven (q : XiZeroCopy) :
    canonicalProjection (deningerDivisorTheta (orbitEven q)) =
      orbitCenter q • orbitEven q := by
  rw [theta_orbitEven, canonicalProjection_apply]
  simp only [map_add, map_smul, monodromy_orbitEven,
    monodromy_orbitOdd, smul_neg]
  module

theorem orbitCenter_re (q : XiZeroCopy) : (orbitCenter q).re = 1 / 2 := by
  rw [orbitCenter_eq]
  simp

/-- On every invariant vector, compression discards exactly the displacement coupling. -/
theorem compressed_theta_on_invariants (x : DeningerDivisorH1)
    (hx : deningerDivisorMonodromy x = x) :
    canonicalProjection (deningerDivisorTheta x) = finsuppDiagonal orbitCenter x := by
  ext q
  have hxq := congrArg (fun y : DeningerDivisorH1 => y q) hx
  rw [divisorMonodromy_apply] at hxq
  simp only [canonicalProjection_apply, Finsupp.smul_apply, Finsupp.add_apply,
    smul_eq_mul, divisorMonodromy_apply, deningerDivisorTheta, finsuppDiagonal_apply]
  rw [hxq]
  simp only [monodromyIndex, deningerDivisorThetaEigen_monodromy, orbitCenter]
  ring

/-- The compressed point spectrum is exactly the critical-line projection of the Xi divisor. -/
theorem compressed_eigenvalue_iff (lam : ℂ) :
    (∃ x : DeningerDivisorH1, x ≠ 0 ∧ deningerDivisorMonodromy x = x ∧
      canonicalProjection (deningerDivisorTheta x) = lam • x) ↔
        ∃ q : XiZeroCopy, orbitCenter q = lam := by
  constructor
  · rintro ⟨x, hx0, hx, heig⟩
    obtain ⟨q, hq⟩ : ∃ q : XiZeroCopy, x q ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (Finsupp.ext h)
    rw [compressed_theta_on_invariants x hx] at heig
    have heq := congrArg (fun y : DeningerDivisorH1 => y q) heig
    simp only [finsuppDiagonal_apply, Finsupp.smul_apply, smul_eq_mul] at heq
    refine ⟨q, ?_⟩
    have hdiv := congrArg (fun z : ℂ => z / x q) heq
    simpa [hq] using hdiv
  · rintro ⟨q, rfl⟩
    exact ⟨orbitEven q, orbitEven_ne_zero q, monodromy_orbitEven q,
      compressed_theta_orbitEven q⟩

/-- All compressed eigenvalues are pure, independently of stability under Frobenius. -/
theorem compressed_eigenvalues_pure (lam : ℂ) :
    (∃ x : DeningerDivisorH1, x ≠ 0 ∧ deningerDivisorMonodromy x = x ∧
      canonicalProjection (deningerDivisorTheta x) = lam • x) → lam.re = 1 / 2 := by
  rw [compressed_eigenvalue_iff]
  rintro ⟨q, rfl⟩
  exact orbitCenter_re q

/-- Frobenius preserves the canonical invariant subspace exactly when RH holds. -/
theorem invariant_subspace_stable_iff_riemannHypothesis :
    (∀ x : DeningerDivisorH1, deningerDivisorMonodromy x = x →
      deningerDivisorMonodromy (deningerDivisorTheta x) = deningerDivisorTheta x) ↔
        RiemannHypothesis := by
  constructor
  · intro hstable
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    have heq : deningerDivisorThetaEigen q =
        deningerDivisorThetaEigen (monodromyIndex q) := by
      classical
      by_cases hq : monodromyIndex q = q
      · rw [hq]
      · have hs := hstable (orbitEven q) (monodromy_orbitEven q)
        simp only [orbitEven, map_add, deningerDivisorTheta_single,
          deningerDivisorMonodromy_single, mul_one] at hs
        change Finsupp.single (monodromyIndex q) (deningerDivisorThetaEigen q) +
          Finsupp.single (monodromyIndex (monodromyIndex q))
            (deningerDivisorThetaEigen (monodromyIndex q)) =
          Finsupp.single q (deningerDivisorThetaEigen q) +
          Finsupp.single (monodromyIndex q)
            (deningerDivisorThetaEigen (monodromyIndex q)) at hs
        rw [monodromyIndex_involutive] at hs
        have hv := congrArg (fun x : DeningerDivisorH1 => x (monodromyIndex q)) hs
        simpa [hq, Ne.symm hq] using hv
    rw [monodromyIndex, deningerDivisorThetaEigen_monodromy] at heq
    have hre := congrArg Complex.re heq
    simp only [sub_re, one_re, conj_re] at hre
    linarith only [hre]
  · intro hRH x hx
    rw [← deningerDivisorMonodromy_comm_of_riemannHypothesis hRH x, hx]

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
