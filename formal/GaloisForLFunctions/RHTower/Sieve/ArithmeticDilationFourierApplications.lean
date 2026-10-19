import GaloisForLFunctions.RHTower.Sieve.FiniteMultiplicativeDilation
import GaloisForLFunctions.RHTower.PowerSievedLiouvilleDirichlet
import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping

/-!
# Short dilation expansions for the corpus's arithmetic sources

The finite Fourier refinement of the paper's Lemma 18.2 applies directly to the
existing complex Liouville function, the sieve's complex Mobius function, and
every power-sieved Liouville family member. Reconstruction reuses the existing
multiplicative factorization theorem; no new arithmetic source is introduced.

For any finite weighted sampling, one explicit phase component dominates the
dilated source sum with no coefficient loss. The components are multiplicative
and 1-bounded for Liouville, Mobius, and the power-sieved family with power at
least two. No cancellation or analytic asymptotic is assumed.
-/

open Finset
namespace RHTower.Sieve
open GaloisForLFunctions.HTGeometry
noncomputable section

private theorem localEuler_primePower_reconstruction (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) : localEuler (fun p k => f (p ^ k)) = f := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  · change (if n = 0 then 0 else ∏ p ∈ n.primeFactors, f (p ^ n.factorization p)) = f n
    rw [if_neg hn, hf.multiplicative_factorization f hn, Finsupp.prod,
      Nat.support_factorization]

/-- The existing complex Liouville source is reconstructed from its local data. -/
theorem localEuler_liouvilleC :
    localEuler (fun p k => _root_.RHTower.liouvilleC (p ^ k)) =
      _root_.RHTower.liouvilleC :=
  localEuler_primePower_reconstruction _ _root_.RHTower.isMultiplicative_liouvilleC

/-- Every dilation of Liouville has a coefficient-mass-one Fourier expansion. -/
theorem liouvilleC_dilation_eq_fourier_components (a n : ℕ) :
    primeSourceDilation (a + 1) _root_.RHTower.liouvilleC n =
      ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        topFourierWeight (a + 1).primeFactors.card h *
          dilationPhaseComponent (fun p k => _root_.RHTower.liouvilleC (p ^ k))
            a (ZMod.stdAddChar h) n := by
  simpa only [localEuler_liouvilleC] using primeSourceDilation_eq_fourier_components
    (fun p k => _root_.RHTower.liouvilleC (p ^ k)) a n

theorem norm_liouvilleC_dilationPhaseComponent_le_one (a n : ℕ) (z : Circle) :
    ‖dilationPhaseComponent (fun p k => _root_.RHTower.liouvilleC (p ^ k))
      a (z : ℂ) n‖ ≤ 1 :=
  norm_dilationPhaseComponent_unitDisk_le_one
    (fun p k => ⟨_, _root_.RHTower.norm_liouvilleC_le_one (p ^ k)⟩) a n z

/-- The existing sieve's Möbius source is reconstructed from its local data. -/
theorem localEuler_moebiusC (n : ℕ) :
    localEuler (fun p k => moebiusC (p ^ k)) n = moebiusC n := by
  have heq := localEuler_primePower_reconstruction
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
    ArithmeticFunction.isMultiplicative_moebius.intCast
  have hn := congrArg (fun f : ArithmeticFunction ℂ => f n) heq
  simpa only [moebiusC, ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast] using hn

/-- Möbius dilations use the same short Fourier expansion, with their actual sieve source. -/
theorem moebiusC_dilation_eq_fourier_components (a n : ℕ) :
    primeSourceDilation (a + 1) moebiusC n =
      ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        topFourierWeight (a + 1).primeFactors.card h *
          dilationPhaseComponent (fun p k => moebiusC (p ^ k))
            a (ZMod.stdAddChar h) n := by
  simpa only [primeSourceDilation, localEuler_moebiusC] using
    primeSourceDilation_eq_fourier_components (fun p k => moebiusC (p ^ k)) a n

theorem norm_moebiusC_dilationPhaseComponent_le_one (a n : ℕ) (z : Circle) :
    ‖dilationPhaseComponent (fun p k => moebiusC (p ^ k)) a (z : ℂ) n‖ ≤ 1 :=
  norm_dilationPhaseComponent_unitDisk_le_one
    (fun p k => ⟨_, norm_moebiusC_le_one (p ^ k)⟩) a n z

/-- Reconstruction for every member of the existing power-sieved Liouville family. -/
theorem localEuler_sievedLiouville (m : ℕ) :
    localEuler (fun p k => sievedLiouville m (p ^ k)) = sievedLiouville m :=
  localEuler_primePower_reconstruction _ (isMultiplicative_sievedLiouville m)

/-- The expansion holds uniformly across the whole power-sieved family. -/
theorem sievedLiouville_dilation_eq_fourier_components (m a n : ℕ) :
    primeSourceDilation (a + 1) (sievedLiouville m) n =
      ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        topFourierWeight (a + 1).primeFactors.card h *
          dilationPhaseComponent (fun p k => sievedLiouville m (p ^ k))
            a (ZMod.stdAddChar h) n := by
  simpa only [localEuler_sievedLiouville] using primeSourceDilation_eq_fourier_components
    (fun p k => sievedLiouville m (p ^ k)) a n

/-- Every member with power at least two has 1-bounded Fourier components. -/
theorem norm_sievedLiouville_dilationPhaseComponent_le_one
    (m a n : ℕ) (z : Circle) :
    ‖dilationPhaseComponent (fun p k => sievedLiouville (m + 2) (p ^ k))
      a (z : ℂ) n‖ ≤ 1 :=
  norm_dilationPhaseComponent_unitDisk_le_one
    (fun p k => ⟨_, norm_sievedLiouville_le_one (by omega) (p ^ k)⟩) a n z

/-- A Liouville dilation correlation is dominated by one of the explicit phase components. -/
theorem exists_liouvilleC_dilationPhaseComponent_norm_sum_ge {I : Type*}
    (a : ℕ) (S : Finset I) (ν : I → ℕ) (w : I → ℂ) :
    ∃ h : ZMod ((a + 1).primeFactors.card + 1),
      ‖∑ i ∈ S, w i * primeSourceDilation (a + 1) _root_.RHTower.liouvilleC (ν i)‖ ≤
        ‖∑ i ∈ S, w i * dilationPhaseComponent
          (fun p k => _root_.RHTower.liouvilleC (p ^ k)) a (ZMod.stdAddChar h) (ν i)‖ := by
  simpa only [localEuler_liouvilleC] using exists_dilationPhaseComponent_norm_sum_ge
    (fun p k => _root_.RHTower.liouvilleC (p ^ k)) a S ν w

/-- The same reduction applies to the existing sieve's Möbius correlations. -/
theorem exists_moebiusC_dilationPhaseComponent_norm_sum_ge {I : Type*}
    (a : ℕ) (S : Finset I) (ν : I → ℕ) (w : I → ℂ) :
    ∃ h : ZMod ((a + 1).primeFactors.card + 1),
      ‖∑ i ∈ S, w i * primeSourceDilation (a + 1) moebiusC (ν i)‖ ≤
        ‖∑ i ∈ S, w i * dilationPhaseComponent
          (fun p k => moebiusC (p ^ k)) a (ZMod.stdAddChar h) (ν i)‖ := by
  simpa only [primeSourceDilation, localEuler_moebiusC] using
    exists_dilationPhaseComponent_norm_sum_ge (fun p k => moebiusC (p ^ k)) a S ν w

/-- Every power-sieved Liouville family member admits the reduction without coefficient loss. -/
theorem exists_sievedLiouville_dilationPhaseComponent_norm_sum_ge {I : Type*}
    (m a : ℕ) (S : Finset I) (ν : I → ℕ) (w : I → ℂ) :
    ∃ h : ZMod ((a + 1).primeFactors.card + 1),
      ‖∑ i ∈ S, w i * primeSourceDilation (a + 1) (sievedLiouville m) (ν i)‖ ≤
        ‖∑ i ∈ S, w i * dilationPhaseComponent
          (fun p k => sievedLiouville m (p ^ k)) a (ZMod.stdAddChar h) (ν i)‖ := by
  simpa only [localEuler_sievedLiouville] using exists_dilationPhaseComponent_norm_sum_ge
    (fun p k => sievedLiouville m (p ^ k)) a S ν w

end
end RHTower.Sieve
