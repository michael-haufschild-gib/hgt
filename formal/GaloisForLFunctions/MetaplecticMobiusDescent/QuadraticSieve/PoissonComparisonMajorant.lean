/-
The Poisson comparison majorant adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.RetainedDualMajorants

/-!
# The Poisson comparison majorant

Euler densities contract column coefficients and principal densities cancel up to the
squarefree cutoff boundary. All retained, tail, source and boundary terms satisfy one centered
Poisson estimate `poissonComparisonMajorant`; annular lifting of high squarefree energy.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

def sourcePrincipalScale (M : ℝ) (I : Ideal O) : ℝ := Real.sqrt (M/(Ideal.absNorm I:ℝ))

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def maskedSourceDensity (G : Ideal O) (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ((sourcePrincipalScale M (rows i).val:ℝ):ℂ)*primeSupportDensity (G*((cols j).val*(cols k).val))

def maskedPrincipalSourceSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal) (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ∑' z : O, rowCoprimeMask (fun P : primeSupport (G*((cols j).val*(cols k).val)) => P.val) Finset.univ z *
      (if z=0 then 0 else W (‖ringComplex z‖^2/sourcePrincipalScale M (rows i).val))

def maskedSourcePrincipalTruncation (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal) (a : n → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    principalTruncation (fun P : primeSupport (G*((cols j).val*(cols k).val)) => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i).val) (Z i)

def maskedSourceErrorSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal) (a : n → ℂ) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    truncationError (fun P : primeSupport (G*((cols j).val*(cols k).val)) => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i).val)
      (sourcePrincipalScale M (rows i).val/T)
      (T*sourcePrincipalScale M (rows i).val) (T^4)

omit [DecidableEq m] [DecidableEq n] in
theorem maskedSourcePrincipalTruncation_eq (G : Ideal O) (hG : Squarefree G)
    (W : 𝓢(ℝ,ℂ)) (hW : W 0=0) (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (a : n → ℂ) (M : ℝ) (Z : m → ℝ)
     (hGc : ∀ j, IsCoprime G (cols j).val) :
    maskedSourcePrincipalTruncation G W rows cols a M Z =
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
      paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z := by
  classical
  have ht (i : m) (j k : n) :
      originalTerm rows cols cols a a 1 1 i j k *
        principalTruncation (fun P : primeSupport (G*((cols j).val*(cols k).val)) => P.val) Finset.univ W
          (sourcePrincipalScale M (rows i).val) (Z i) =
      paperRadialFourier W 0*(originalTerm rows cols cols a a 1 1 i j k *
        ((sourcePrincipalScale M (rows i).val:ℝ):ℂ)*primeSupportDensity (G*((cols j).val*(cols k).val))) -
      paperRadialFourier W 0*(originalTerm rows cols cols a a 1 1 i j k *
        ∑ d ∈ idealDivisors (G*((cols j).val*(cols k).val)), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((sourcePrincipalScale M (rows i).val/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) := by
    by_cases hc : (cols j).val ⊔ (cols k).val = ⊤
    · have hC : Squarefree ((cols j).val*(cols k).val) := squarefree_mul_iff.mpr
        ⟨(Ideal.isCoprime_iff_sup_eq.mpr hc).isRelPrime,(cols j).property.2.1,(cols k).property.2.1⟩
      have hprod : Squarefree (G*((cols j).val*(cols k).val)) := squarefree_mul_iff.mpr
        ⟨((hGc j).mul_right (hGc k)).isRelPrime,hG,hC⟩
      have hp := principalTruncation_scaled (G*((cols j).val*(cols k).val)) hprod W 1
        (sourcePrincipalScale M (rows i).val) (Z i)
      simp only [Complex.ofReal_one,one_mul,hW,zero_mul,sub_zero] at hp
      rw [hp]
      ring
    · have hz : originalTerm rows cols cols a a 1 1 i j k=0 := by simp only [originalTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold maskedSourcePrincipalTruncation
  simp_rw [ht]
  simp only [maskedSourceDensity,maskedPrincipalDivisorCorrection,sourcePrincipalScale,Finset.sum_sub_distrib,Finset.mul_sum]

omit [DecidableEq m] [DecidableEq n] in
theorem maskedPrincipalSourceSum_eq (G : Ideal O) (hG : Squarefree G)
    (W : 𝓢(ℝ,ℂ)) (hW : W 0=0) (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (a : n → ℂ) (M T : ℝ)
     (hGc : ∀ j, IsCoprime G (cols j).val) :
    maskedPrincipalSourceSum G W rows cols a M =
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
      paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M
        (fun i => T*sourcePrincipalScale M (rows i).val) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M
        (fun i => sourcePrincipalScale M (rows i).val/T)
        (fun i => T*sourcePrincipalScale M (rows i).val) (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by
  rw [←maskedSourcePrincipalTruncation_eq G hG W hW rows cols a M _ hGc]
  unfold maskedPrincipalSourceSum maskedSourcePrincipalTruncation originalMaskedTruncatedMiddle maskedSourceErrorSum
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold truncationError sourcePrincipalScale
  ring



theorem maskedSource_error_uniform (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal),
        Function.Injective rows → Function.Injective cols →
        (∀ i, (Ideal.absNorm (rows i).val:ℝ)≤B) →
        (∀ j, (Ideal.absNorm (cols j).val:ℝ)≤N) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖maskedSourceErrorSum G W rows cols a M T‖ ≤
          (diagonalControl sieveCutoff)^2*B*N*((divisorConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
            (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := primeSupport_truncation_error_bound l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols a W
  let E := (divisorConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l
  let error := fun i j k =>
    truncationError (fun P : primeSupport (G*((cols j).val*(cols k).val)) => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i).val) (sourcePrincipalScale M (rows i).val/T)
      (T*sourcePrincipalScale M (rows i).val) (T^4)
  have hs := (divisorConstant_pos ε hε).le
  have hE : 0≤E := by dsimp only [E]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖≤E := by
    have hi : 0<(Ideal.absNorm (rows i).val:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal _ (rows i).property.1))
    have hX : 0<sourcePrincipalScale M (rows i).val := Real.sqrt_pos.mpr (div_pos hM hi)
    have h := hbound ε hε (G*((cols j).val*(cols k).val))
      (mul_ne_zero hG (mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1) (primaryIdealGenerator_ne_zero_ideal _ (cols k).property.1))) W
      (sourcePrincipalScale M (rows i).val) (sourcePrincipalScale M (rows i).val) T hX
      (by linarith) (by linarith) hT
    simp only [map_mul,Nat.cast_mul] at h
    apply h.trans
    dsimp only [E]
    gcongr
    · exact hcols j
    · exact hcols k
  exact original_pair_error_ideal_bound rows cols hr hc B N hB hN hrows hcols a E hE error herr


def sourcePrincipalMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*((idealDivisors G).card *
    (((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (4*N/T+Real.sqrt M*B^(α-1/2))))) +
  (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
    ((2*nonzeroLatticeEnvelopeConstant*originalMiddleDecayConstant W)*
      divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (N+(2*T)*Real.sqrt M*B^(α-1/2)))) +
  (diagonalControl sieveCutoff)^2*B*N*((divisorConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2

theorem masked_source_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal),
        Function.Injective rows → Function.Injective cols →
        (∀ i, B/2≤(Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ)≤B) →
        (∀ j, (Ideal.absNorm (cols j).val:ℝ)≤N) →
        (∀ j, IsCoprime G (cols j).val) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W rows cols a M -
          paperRadialFourier W 0*maskedSourceDensity G rows cols a M‖ ≤
        sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  obtain ⟨s,C,hC,herr⟩ := maskedSource_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols hGc a W hW
  let Z := fun i => T*sourcePrincipalScale M (rows i).val
  let Y := fun i => sourcePrincipalScale M (rows i).val/T
  have hT0 : 0≤T := by linarith
  have hsplit := maskedPrincipalSourceSum_eq G hG W hW rows cols a M T hGc
  change maskedPrincipalSourceSum G W rows cols a M =
    paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
    paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z +
    originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
    maskedSourceErrorSum G W rows cols a M T at hsplit
  have heq : maskedPrincipalSourceSum G W rows cols a M -
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M =
      -(paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by rw [hsplit]; ring
  have hl := hexp.masked_source_large_principal_sum deltaLoss hδ ε hε G hG.ne_zero B N M T hB hN hM (by linarith)
    rows cols cols hr hc hc hrows hcols hcols hGc hGc a a Z (fun _ => le_rfl)
  have hm := hexp.original_masked_truncated_middle deltaLoss hδ ε hε G hG B N M T hB hN hM hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hGc hGc (fun _ => le_rfl)
  have he := herr ε hε G hG.ne_zero B N M T hB hN hM hT rows cols hr hc
    (fun i => (hrows i).2) hcols a W
  have hn := norm_four_correction_terms
    (paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) 0
    (originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4))
    (maskedSourceErrorSum G W rows cols a M T)
  simp only [sub_zero,norm_zero,add_zero] at hn
  rw [heq]
  apply hn.trans
  rw [norm_mul]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) hm) he

lemma sourcePrincipalMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (_hM : 0≤M) (hT : 0≤T) :
    0 ≤ sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (divisorConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := originalMiddleDecayConstant_nonneg W
  unfold sourcePrincipalMajorant
  positivity

lemma sourcePrincipalMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B' B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (_hM : 0≤M) (hT : 0≤T) :
    sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B' N M T a W ≤
      sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (divisorConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := originalMiddleDecayConstant_nonneg W
  unfold sourcePrincipalMajorant
  gcongr

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

lemma maskedPrincipalSourceDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (hS : ∀ I ∈ S, quadraticIdealAdmissible I) (K : ℝ)
    (cols : n → QuadraticIdeal) (a : n → ℂ) (M : ℝ) :
    maskedPrincipalSourceSum G W (fun I : S => (⟨I.val, hS I.val I.property⟩ : QuadraticIdeal)) cols a M -
      paperRadialFourier W 0*maskedSourceDensity G (fun I : S => (⟨I.val, hS I.val I.property⟩ : QuadraticIdeal)) cols a M =
    ∑ j : Fin (columnDyadicLength K+1),
      (maskedPrincipalSourceSum G W (fun I : divisorDyadicBin S K j => (⟨I.val, hS I.val (Finset.mem_filter.mp I.property).1⟩ : QuadraticIdeal)) cols a M -
        paperRadialFourier W 0*maskedSourceDensity G (fun I : divisorDyadicBin S K j => (⟨I.val, hS I.val (Finset.mem_filter.mp I.property).1⟩ : QuadraticIdeal)) cols a M) := by
  classical
  let term (I : Ideal O) (j k : n) : ℂ :=
    if (cols j).val ⊔ (cols k).val = ⊤ then
      star (canonicalQuadraticRow (cols j) (primaryIdealGenerator I) * a j) *
        (canonicalQuadraticRow (cols k) (primaryIdealGenerator I) * a k) else 0
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    (∑ j, ∑ k, term I j k * ∑' z : O,
      rowCoprimeMask (fun P : primeSupport (G*((cols j).val*(cols k).val)) => P.val) Finset.univ z *
        (if z=0 then 0 else W (‖ringComplex z‖^2/sourcePrincipalScale M I))) -
    paperRadialFourier W 0 * ∑ j, ∑ k, term I j k *
      ((sourcePrincipalScale M I : ℝ) : ℂ) * primeSupportDensity (G*((cols j).val*(cols k).val)))
  simpa only [maskedPrincipalSourceSum, maskedSourceDensity, originalTerm, term,
    one_dvd, ite_true, Finset.mul_sum, ← Finset.sum_sub_distrib] using h

theorem masked_source_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), Squarefree G →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (S : Finset (Ideal O)) (hS : ∀ I∈S, quadraticIdealAdmissible I ∧ (Ideal.absNorm I:ℝ)≤K),
      ∀ (cols : n → QuadraticIdeal), Function.Injective cols →
        (∀ j, (Ideal.absNorm (cols j).val:ℝ)≤N) →
        (∀ j, IsCoprime G (cols j).val) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W (fun I : S => (⟨I.val, (hS I.val I.property).1⟩ : QuadraticIdeal)) cols a M -
          paperRadialFourier W 0*maskedSourceDensity G (fun I : S => (⟨I.val, (hS I.val I.property).1⟩ : QuadraticIdeal)) cols a M‖ ≤
        (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G (2*K) N M T a W := by
  obtain ⟨s,C,hC,hbound⟩ := masked_source_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT S hS cols hc hcols hGc a W hW
  classical
  let R := sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G (2*K) N M T a W
  have hSnorm (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := hS I hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal _ hi.1.1))
  have hR : 0≤R := sourcePrincipalMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε G (2*K) N M T a W
    (by linarith) (by linarith) hM.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖maskedPrincipalSourceSum G W (fun I : divisorDyadicBin S K j => (⟨I.val, (hS I.val (Finset.mem_filter.mp I.property).1).1⟩ : QuadraticIdeal)) cols a M -
        paperRadialFourier W 0*maskedSourceDensity G (fun I : divisorDyadicBin S K j => (⟨I.val, (hS I.val (Finset.mem_filter.mp I.property).1).1⟩ : QuadraticIdeal)) cols a M‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hSnorm j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : quadraticIdealAdmissible I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hSnorm j I.val I.property
        refine ⟨(hS I.val (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT
        (fun I : divisorDyadicBin S K j => (⟨I.val, (hS I.val (Finset.mem_filter.mp I.property).1).1⟩ : QuadraticIdeal)) cols (fun I J h => Subtype.ext (congrArg (fun K : QuadraticIdeal => K.val) h)) hc (fun I => (hrows I).2) hcols hGc a W hW
      apply hh.trans
      exact sourcePrincipalMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε G B (2*K) N M T a W
        (by linarith) hBK (by linarith) hM.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [maskedPrincipalSourceSum,maskedSourceDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [maskedPrincipalSourceDifference_dyadic G W S (fun I hI => (hS I hI).1) K cols a M]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson UniqueFactorizationMonoid
open scoped SchwartzMap

theorem primeSupportDensity_eq_support (G : Ideal O) :
    primeSupportDensity G = ∏ P ∈ primeSupport G, (1-(1:ℂ)/(Ideal.absNorm P:ℂ)) :=
  Finset.prod_coe_sort (s := primeSupport G)
    (f := fun P : Ideal O => (1-(1:ℂ)/(Ideal.absNorm P:ℂ)))

lemma primeSupportDensity_factor_norm (P : Ideal O) (hP : P ≠ 0) :
    ‖(1 : ℂ) - 1 / (Ideal.absNorm P : ℂ)‖ ≤ 1 := by
  have hn : (1 : ℝ) ≤ Ideal.absNorm P := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  have hp : (0 : ℝ) < Ideal.absNorm P := lt_of_lt_of_le zero_lt_one hn
  have hi : (1 : ℝ) / Ideal.absNorm P ≤ 1 := (div_le_one hp).mpr hn
  have he : (1 : ℂ) - 1 / (Ideal.absNorm P : ℂ) =
      ((1 - 1 / (Ideal.absNorm P : ℝ) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hi)]
  exact sub_le_self _ (by positivity)

/-- Every Euler density is a contraction on column coefficients. -/
theorem primeSupportDensity_norm_le_one (G : Ideal O) : ‖primeSupportDensity G‖ ≤ 1 := by
  rw [primeSupportDensity_eq_support, norm_prod]
  exact Finset.prod_le_one (fun P _ => norm_nonneg _)
    (fun P hP => primeSupportDensity_factor_norm P (support_prime hP).ne_zero)

theorem primeSupportDensity_star (G : Ideal O) : star (primeSupportDensity G) = primeSupportDensity G := by
  simp [primeSupportDensity]

theorem primeSupportDensity_mul (G H : Ideal O) (hG : G ≠ 0) (hH : H ≠ 0)
    (hcop : IsCoprime G H) : primeSupportDensity (G*H) = primeSupportDensity G*primeSupportDensity H := by
  simp only [primeSupportDensity_eq_support,primeSupport]
  rw [normalizedFactors_mul hG hH,Multiset.toFinset_add,Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro P hPG hPH
  exact (Multiset.disjoint_left.mp (disjoint_normalizedFactors hcop.isRelPrime))
    (Multiset.mem_toFinset.mp hPG) (Multiset.mem_toFinset.mp hPH)

lemma quadraticIdealMask_generator_eq_one (I : QuadraticIdeal) (G : Ideal O)
    (hcop : IsCoprime I.val G) : quadraticIdealMask I (cubicIdealGenerator G) = 1 := by
  rw [quadraticIdealMask_indicator, span_cubicIdealGenerator, if_pos hcop.symm]

theorem quadraticPairDensity_eq_primeSupportDensity (I J : QuadraticIdeal) (G : Ideal O)
    (hI : IsCoprime I.val G) (hJ : IsCoprime J.val G) :
    quadraticPairDensity I J G = primeSupportDensity G := by
  rw [quadraticPairDensity,primeSupportDensity_eq_support]
  apply Finset.prod_congr rfl
  intro P hP
  have hPG : P ∣ G := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  rw [quadraticIdealMask_generator_eq_one I P (hI.of_isCoprime_of_dvd_right hPG),
    quadraticIdealMask_generator_eq_one J P (hJ.of_isCoprime_of_dvd_right hPG),one_mul]

def densityColumn {n : Type*} (cols : n → QuadraticIdeal) (a : n → ℂ) : n → ℂ :=
  fun j => primeSupportDensity (cols j).val * a j

theorem densityColumn_norm_le {n : Type*} (cols : n → QuadraticIdeal) (a : n → ℂ)
    (j : n) : ‖densityColumn cols a j‖ ≤ ‖a j‖ := by
  rw [densityColumn,norm_mul]
  exact (mul_le_mul_of_nonneg_right (primeSupportDensity_norm_le_one _) (norm_nonneg _)).trans_eq (one_mul _)

theorem densityColumn_energy_le {n : Type*} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) :
    (∑ j, ‖densityColumn cols a j‖^2) ≤ ∑ j, ‖a j‖^2 :=
  Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (densityColumn_norm_le cols a j) 2)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson UniqueFactorizationMonoid DivisorBlockCauchy
open scoped SchwartzMap

theorem principalDifference_densityColumn {n : Type*} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (D : Ideal O) (K : ℝ)
     (hcop : ∀ j, IsCoprime (cols j).val (quadraticMaskIdeal D)) :
    principalDifference cols (densityColumn cols a) D K =
      (∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
        star (a j)*a k*primeSupportDensity ((cols j).val*(cols k).val)*
          (quadraticPairPartial (cols j) (cols k) K * quadraticPairDivisors (cols j) (cols k) (quadraticMaskIdeal D))
        else 0) -
      primeSupportDensity (quadraticMaskIdeal D) * (∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
        star (a j)*a k*primeSupportDensity ((cols j).val*(cols k).val)*
          quadraticPairCoprimePartial (cols j) (cols k) (quadraticMaskIdeal D) K else 0) := by
  unfold principalDifference
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : IsCoprime (cols j).val (cols k).val
  · simp only [hjk,ite_true,densityColumn,star_mul,primeSupportDensity_star,
      primeSupportDensity_mul _ _ (primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1) (primaryIdealGenerator_ne_zero_ideal _ (cols k).property.1) hjk,
      quadraticPairDensity_eq_primeSupportDensity _ _ _ (hcop j) (hcop k)]
    ring
  · simp only [hjk,ite_false,mul_zero,sub_self]

def densityPairSum {n : Type} [Fintype n] (cols : n → QuadraticIdeal) (a : n → ℂ)
    (P : QuadraticIdeal → QuadraticIdeal → ℂ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
    star (a j)*a k*primeSupportDensity ((cols j).val*(cols k).val)*P (cols j) (cols k) else 0

theorem unrestrictedPrincipalDensity_eq {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    unrestrictedPrincipalDensity rows cols cols a a R =
      (Real.sqrt R : ℂ)*densityPairSum cols a
        (fun I J => ∑ i, normalizedQuadraticPair I J (rows i)) := by
  unfold unrestrictedPrincipalDensity
  rw [Finset.sum_comm]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j).val (cols k).val
  · simp only [unrestrictedPairTerm, ← Ideal.isCoprime_iff_sup_eq,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sqrt_div hR]
    simp only [Complex.ofReal_div,normalizedQuadraticPair]
    ring
  · simp only [unrestrictedPairTerm, ← Ideal.isCoprime_iff_sup_eq,hc,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]

theorem unrestrictedPrincipalDensity_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (R K : ℝ) (hR : 0 ≤ R) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealBall K => I.val) cols cols a a R =
      (Real.sqrt R : ℂ)*densityPairSum cols a (fun I J => quadraticPairPartial I J K) := by
  simpa only [quadraticPairPartial] using
    unrestrictedPrincipalDensity_eq (fun I : squarefreeIdealBall K => I.val) cols a R hR


theorem originalTerm_one_eq_unrestricted {m n : Type*}
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (hray : ∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k)) (i : m) (j k : n) :
    originalTerm rows cols cols a a 1 1 i j k =
      unrestrictedPairTerm (fun i => (rows i).val) cols cols a a i j k := by
  by_cases hc : (cols j).val ⊔ (cols k).val = ⊤
  · simp only [originalTerm, unrestrictedPairTerm, hc, ite_true, one_dvd, star_mul,
      canonicalQuadraticRow_star,
      canonicalQuadraticPairIdeal_primary (cols j) (cols k) (hray j k) (rows i).val (rows i).property.1]
    ring
  · simp only [originalTerm, unrestrictedPairTerm, hc, ite_false]

theorem maskedSourceDensity_eq {m n : Type} [Fintype m] [Fintype n]
    (G : Ideal O) (hG : G ≠ 0) (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (a : n → ℂ) (M : ℝ) (hray : ∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j).val) :
    maskedSourceDensity G rows cols a M =
      primeSupportDensity G * unrestrictedPrincipalDensity (fun i => (rows i).val) cols cols a a M := by
  simp only [maskedSourceDensity, unrestrictedPrincipalDensity, Finset.mul_sum, sourcePrincipalScale]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [originalTerm_one_eq_unrestricted rows cols a hray]
  rw [primeSupportDensity_mul G ((cols j).val * (cols k).val) hG
    (mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1)
      (primaryIdealGenerator_ne_zero_ideal _ (cols k).property.1)) ((hGc j).mul_right (hGc k))]
  ring

theorem maskedSourceDensity_coprime_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (K M : ℝ) (hM : 0 ≤ M) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (hray : ∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k))
    (hGc : ∀ j, IsCoprime (quadraticMaskIdeal D) (cols j).val) :
    maskedSourceDensity (quadraticMaskIdeal D)
      (fun I : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K =>
        (⟨I.val, coprimeSquarefreeIdealBall_admissible D K I⟩ : QuadraticIdeal)) cols a M =
      (Real.sqrt M : ℂ) * primeSupportDensity (quadraticMaskIdeal D) * densityPairSum cols a
        (fun I J => quadraticPairCoprimePartial I J (quadraticMaskIdeal D) K) := by
  rw [maskedSourceDensity_eq _ (quadraticMaskIdeal_squarefree D).ne_zero _ cols a M hray hGc,
    unrestrictedPrincipalDensity_eq _ _ _ _ hM]
  unfold quadraticPairCoprimePartial
  ring

theorem unrestrictedPrincipalDensity_twisted_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (q : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
     :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealBall K => I.val) cols cols
      (fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q))
      (fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q)) (M/(Ideal.absNorm q:ℝ)) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => quadraticPairPartial I J K*normalizedQuadraticPair I J q) := by
  rw [unrestrictedPrincipalDensity_squarefree _ _ _ _ (by positivity),Real.sqrt_div hM]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j).val (cols k).val
  · simp only [hc,ite_true,star_mul,canonicalQuadraticRow_star,
      normalizedQuadraticPair,canonicalQuadraticPairIdeal,Complex.ofReal_div]
    ring
  · simp only [hc,ite_false,mul_zero]

theorem densityPairSum_weighted_sum {n : Type} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P : QuadraticIdeal → QuadraticIdeal → ℂ) (Q : ι → QuadraticIdeal → QuadraticIdeal → ℂ) :
    (∑ q ∈ S, c q*densityPairSum cols a (fun I J => P I J*Q q I J)) =
      densityPairSum cols a (fun I J => P I J*∑ q ∈ S, c q*Q q I J) := by
  simp only [densityPairSum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j).val (cols k).val
  · simp only [hc,ite_true]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero]

theorem summed_dual_density {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (G : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
     :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealBall K => I.val) cols cols
        (fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q))
        (fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q)) (M/(Ideal.absNorm q:ℝ))) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => quadraticPairPartial I J K*quadraticPairDivisors I J G) := by
  simp_rw [unrestrictedPrincipalDensity_twisted_squarefree cols a _ M K hM]
  calc
    _ = (Real.sqrt M : ℂ)*∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        densityPairSum cols a (fun I J => quadraticPairPartial I J K*normalizedQuadraticPair I J q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl


/-- Principal densities cancel up to the exact squarefree cutoff boundary. -/
theorem source_dual_density_cancellation {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (D : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hray : ∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k))
    (hGc : ∀ j, IsCoprime (quadraticMaskIdeal D) (cols j).val) :
    (∑ q ∈ idealDivisors (quadraticMaskIdeal D), (moebius q : ℂ) *
      unrestrictedPrincipalDensity (fun I : squarefreeIdealBall K => I.val) cols cols
        (fun j => a j * canonicalQuadraticRow (cols j) (cubicIdealGenerator q))
        (fun j => a j * canonicalQuadraticRow (cols j) (cubicIdealGenerator q)) (M / (Ideal.absNorm q : ℝ))) -
      maskedSourceDensity (quadraticMaskIdeal D)
        (fun I : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K =>
          (⟨I.val, coprimeSquarefreeIdealBall_admissible D K I⟩ : QuadraticIdeal)) cols a M =
      (Real.sqrt M : ℂ) * principalDifference cols (densityColumn cols a) D K := by
  rw [summed_dual_density cols a (quadraticMaskIdeal D) M K hM,
    maskedSourceDensity_coprime_squarefree D K M hM cols a hray hGc,
    principalDifference_densityColumn cols a D K (fun j => (hGc j).symm)]
  change _ = (Real.sqrt M : ℂ) * (densityPairSum cols a
    (fun I J => quadraticPairPartial I J K * quadraticPairDivisors I J (quadraticMaskIdeal D)) -
    primeSupportDensity (quadraticMaskIdeal D) * densityPairSum cols a
      (fun I J => quadraticPairCoprimePartial I J (quadraticMaskIdeal D) K))
  ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy

/-- Reciprocal sieve control bounds the remaining principal cutoff discrepancy. -/
theorem HasSieveExponent.principal_difference {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (cols : n → QuadraticIdeal) (hinj : Function.Injective cols)
      (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K →
      (∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N) →
      (∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k)) →
      ∀ (a : n → ℂ) (D : Ideal O) (ε : ℝ) (hε : 0 < ε),
      ‖(Real.sqrt M : ℂ) * principalDifference cols a D K‖ ≤
        ((idealDivisors (quadraticMaskIdeal D)).card : ℝ)^2 * (divisorConstant ε hε * N^ε) *
          C * (K*N)^deltaLoss * (Real.sqrt (M/K)*N + Real.sqrt M*K^(α-1/2)) *
          ∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hbound⟩ := hexp.reverse deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro n _ _ cols hinj M N K hM hN hK hcols hray a D ε hε
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 < K := by linarith
  have hs := principalDifference_bound cols hinj N (by linarith) hcols hray a D K hK0 ε hε
  have hsupp := (divisorConstant_pos ε hε).le
  have hb := hbound K N hK hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ Real.sqrt M * (((idealDivisors (quadraticMaskIdeal D)).card : ℝ)^2 *
        ((1/Real.sqrt K)*sieveNorm K N*(divisorConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt M * (((idealDivisors (quadraticMaskIdeal D)).card : ℝ)^2 *
        ((1/Real.sqrt K)*(C*(K*N)^deltaLoss*(N+K^α))*(divisorConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) := by
      gcongr
    _ = ((idealDivisors (quadraticMaskIdeal D)).card : ℝ)^2*(divisorConstant ε hε*N^ε)*C*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*(N+K^α))*∑ j, ‖a j‖^2 := by
      rw [Real.sqrt_div hM0]
      ring
    _ = _ := by
      rw [mul_add, sqrt_div_mul_rpow M K α hM0 hK0]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson UniqueFactorizationMonoid
open scoped SchwartzMap

def maskedPairIdealDualKernel (G : Ideal O) (I J : QuadraticIdeal) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q/(Ideal.absNorm q:ℂ))*
      ∑' B : NonzeroIdeal, canonicalQuadraticPairIdeal I J B.val*paperRadialFourier W
        ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)))*(Ideal.absNorm B.val:ℝ))

def maskedPairDualTail (G : Ideal O) (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q/(Ideal.absNorm q:ℂ))*
        quadraticDualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ))) K

def retainedDualPair (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ)) (M F K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealBall K, canonicalQuadraticPairIdeal I J B.val*
    (((M/(Real.sqrt ((Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ))*F):ℝ):ℂ)*
      quadraticDualPrincipalIdeal I J W
        (Real.sqrt (F*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)/(M*(Ideal.absNorm B.val:ℝ)))))

theorem maskedPairIdealDualKernel_retained
    (G : Ideal O) (I J : QuadraticIdeal) (hG : G ≠ 0) 
    (hray : quadraticColumnRay I=quadraticColumnRay J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    maskedPairIdealDualKernel G I J W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q*
        retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K) +
      maskedPairDualTail G I J W M K := by
  have hNI : 0<(Ideal.absNorm I.val:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => (primaryIdealGenerator_ne_zero_ideal _ I.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J.val:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => (primaryIdealGenerator_ne_zero_ideal _ J.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
  have hqpos (q : Ideal O) (hq : q ∈ idealDivisors G) : 0<(Ideal.absNorm q:ℝ) := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hpoint (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)):ℂ))*
        (((UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q/(Ideal.absNorm q:ℂ))*
          ∑' B : NonzeroIdeal, canonicalQuadraticPairIdeal I J B.val*paperRadialFourier W
            ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)))*(Ideal.absNorm B.val:ℝ))) =
        (UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q*
          retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K +
        ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)):ℂ))*
          (((UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q/(Ideal.absNorm q:ℂ))*
            quadraticDualSquarefreeTail I J W
              (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ))) K) := by
    have hqN := hqpos q hq
    have ht : 0 < M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)) := by
      positivity
    rw [quadraticDual_low_add_tail I J W _ K ht,quadraticDualSquarefreeLow_principal_finite I J hray W _ K ht,
      mul_add,mul_add]
    congr 1
    simp only [retainedDualPair,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    have hB : 0<(Ideal.absNorm B.val:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr
        (fun hz => (mem_squarefreeIdealBall.mp B.property).1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    have harg : (1:ℝ)/((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)))*(Ideal.absNorm B.val:ℝ)) =
        (Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)/(M*(Ideal.absNorm B.val:ℝ)) := by
      field_simp
    rw [harg]
    push_cast
    ring
  unfold maskedPairIdealDualKernel maskedPairDualTail
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint


theorem retainedDualPrincipalSum_pair_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ) (M F K : ℝ) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealBall K => I.val) cols a M F =
      ∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
        star (a j)*a k*retainedDualPair (cols j) (cols k) W M F K else 0 := by
  unfold retainedDualPrincipalSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j).val (cols k).val
  · simp only [unrestrictedPairTerm, ← Ideal.isCoprime_iff_sup_eq,retainedDualPair,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  · simp only [unrestrictedPairTerm, ← Ideal.isCoprime_iff_sup_eq,hc,ite_false,zero_mul,Finset.sum_const_zero]

theorem retainedDualPrincipalSum_twist_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ) (M F K : ℝ) (q : Ideal O)
     :
    retainedDualPrincipalSum W (fun I : squarefreeIdealBall K => I.val) cols
      (fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q)) M F =
      ∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
        star (a j)*a k*canonicalQuadraticPairIdeal (cols j) (cols k) q*
          retainedDualPair (cols j) (cols k) W M F K else 0 := by
  rw [retainedDualPrincipalSum_pair_expansion]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j).val (cols k).val
  · simp only [hc,ite_true,star_mul,canonicalQuadraticRow_star,canonicalQuadraticPairIdeal]
    ring
  · simp only [hc,ite_false]

def maskedDualFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
    star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0

def maskedDualTailFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
    star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0

theorem maskedDualFamily_retained {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G ≠ 0) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) 
    (hray : ∀ j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k)) :
    maskedDualFamily G cols a W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealBall K => I.val) cols
          (fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily G cols a W M K := by
  have hp (j k : n) :
      (if IsCoprime (cols j).val (cols k).val then
        star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0) =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        (if IsCoprime (cols j).val (cols k).val then
          star (a j)*a k*canonicalQuadraticPairIdeal (cols j) (cols k) q*
            retainedDualPair (cols j) (cols k) (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K
          else 0)) +
      (if IsCoprime (cols j).val (cols k).val then
        star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0) := by
    by_cases hc : IsCoprime (cols j).val (cols k).val
    · simp only [hc,ite_true,maskedPairIdealDualKernel_retained G (cols j) (cols k)
        hG (hray j k) W M K hM,mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      ring
    · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
  simp only [maskedDualFamily,hp,Finset.sum_add_distrib,maskedDualTailFamily]
  congr 1
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [retainedDualPrincipalSum_twist_expansion _ cols a _ _ _ q]
  simp only [Finset.mul_sum]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson UniqueFactorizationMonoid
open scoped SchwartzMap

theorem maskedPairDualTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ (G : Ideal O) (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ)) (M N K : ℝ),
      G≠0 → 0<M → 1≤N → 0≤K →
      N/2≤(Ideal.absNorm I.val:ℝ) → (Ideal.absNorm I.val:ℝ)≤N →
      N/2≤(Ideal.absNorm J.val:ℝ) → (Ideal.absNorm J.val:ℝ)≤N →
      ‖maskedPairDualTail G I J W M K‖ ≤
        (2*M/N)*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := quadraticDualSquarefreeTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro G I J W M N K hG hM hN hK hIl hIu hJl hJu
  have hNG : 0<(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNI : 0<(Ideal.absNorm I.val:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => (primaryIdealGenerator_ne_zero_ideal _ I.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J.val:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => (primaryIdealGenerator_ne_zero_ideal _ J.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
  have hN0 : 0<N := by linarith
  let t0 := M/((Ideal.absNorm G:ℝ)*N*N)
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 t0)^2*(1+t0*K)^A)
  have ht0 : 0<t0 := by dsimp only [t0]; positivity
  have hT : 0≤T := by dsimp only [T]; positivity
  have hterm (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖((UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q/(Ideal.absNorm q:ℂ))*
        quadraticDualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ))) K‖ ≤ T := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hqN : (Ideal.absNorm q:ℝ)≤(Ideal.absNorm G:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by exact_mod_cast hNG) (map_dvd Ideal.absNorm hqG)
    have ht : 0<M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)) := by positivity
    have htlo : t0≤M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)) := by
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      gcongr
    have hc : ‖(UniqueFactorizationMonoid.moebius q:ℂ)*canonicalQuadraticPairIdeal I J q/(Ideal.absNorm q:ℂ)‖≤1 := by
      rw [norm_div,norm_mul,Complex.norm_natCast]
      have hp : ‖canonicalQuadraticPairIdeal I J q‖≤1 := by
        rw [canonicalQuadraticPairIdeal,norm_mul]
        exact (mul_le_mul (canonicalQuadraticRow_norm_le_one _ _) (canonicalQuadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      calc
        _ ≤ (1*1)/(Ideal.absNorm q:ℝ) := by
          gcongr
          exact norm_ideal_moebius_le_one q
        _ ≤ 1 := by simpa only [one_mul,div_one] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1)
    have hb : ‖quadraticDualSquarefreeTail I J W
        (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ))) K‖≤T := by
      apply (hbound I J W _ K ht hK).trans
      dsimp only [T]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    rw [norm_mul]
    exact (mul_le_mul hc hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpref : ‖(M:ℂ)/(Real.sqrt ((Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ)):ℂ)‖≤2*M/N := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM.le,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one,one_mul] using
      dual_truncation_prefactor_bound M 1 N (Ideal.absNorm I.val) (Ideal.absNorm J.val)
        hM (by norm_num) hN0 ⟨hIl,hIu⟩ ⟨hJl,hJu⟩
  rw [maskedPairDualTail,norm_mul]
  calc
    _ ≤ (2*M/N)*(∑ q ∈ idealDivisors G, T) := mul_le_mul hpref
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T,t0]; ring

theorem coprime_pair_error_energy {n : Type} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (E : ℝ) (hE : 0≤E)
    (error : n → n → ℂ) (herr : ∀ j k, ‖error j k‖≤E) :
    ‖∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then star (a j)*a k*error j k else 0‖ ≤
      (Fintype.card n:ℝ)*E*∑ j, ‖a j‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖*‖a k‖*E) = (∑ j, ‖a j‖)^2*E := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ ≤ ∑ j, ∑ k, ‖if IsCoprime (cols j).val (cols k).val then star (a j)*a k*error j k else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, ‖a j‖*‖a k‖*E := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · simp only [norm_mul,norm_star]
        exact mul_le_mul_of_nonneg_left (herr j k) (by positivity)
      · simp only [norm_zero]
        positivity
    _ = (∑ j, ‖a j‖)^2*E := hs
    _ ≤ ((∑ j, ‖a j‖^2)*(Fintype.card n:ℝ))*E := mul_le_mul_of_nonneg_right hcs hE
    _ = _ := by ring

theorem maskedDualTailFamily_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] (G : Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ)
      (W : 𝓢(ℝ,ℂ)) (M N K : ℝ), G≠0 → Function.Injective cols →
      0<M → 1≤N → 0≤K →
      (∀ j, N/2≤(Ideal.absNorm (cols j).val:ℝ) ∧ (Ideal.absNorm (cols j).val:ℝ)≤N) →
      ‖maskedDualTailFamily G cols a W M K‖ ≤
        (2*diagonalControl sieveCutoff)*M*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) * ∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := maskedPairDualTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro n _ G cols a W M N K hG hinj hM hN hK hcols
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)
  have hT : 0≤T := by dsimp only [T]; positivity
  have hn := finite_ideal_family_card_bound (fun j => (cols j).val) (Subtype.val_injective.comp hinj) N hN
    (fun j => (hcols j).2)
  have herr (j k : n) : ‖maskedPairDualTail G (cols j) (cols k) W M K‖≤
      (2*M/N)*(idealDivisors G).card*T :=
    hbound G (cols j) (cols k) W M N K hG hM hN hK
      (hcols j).1 (hcols j).2 (hcols k).1 (hcols k).2
  calc
    _ ≤ (Fintype.card n:ℝ)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 :=
      coprime_pair_error_energy cols a _ (by positivity) _ herr
    _ ≤ (diagonalControl sieveCutoff*N)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 := by gcongr
    _ = _ := by dsimp only [T]; field_simp

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson UniqueFactorizationMonoid DivisorBlockCauchy
open scoped SchwartzMap

def divisorTwist {n : Type} (cols : n → QuadraticIdeal) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*canonicalQuadraticRow (cols j) (cubicIdealGenerator q)

def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (Nat.card Oˣ : ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealBall K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealBall K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))


def centeredMaskedSource {n : Type} [Fintype n]
    (D : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum (quadraticMaskIdeal D) (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K =>
      (⟨I.val, coprimeSquarefreeIdealBall_admissible D K I⟩ : QuadraticIdeal)) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity (quadraticMaskIdeal D)
      (fun I : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K =>
        (⟨I.val, coprimeSquarefreeIdealBall_admissible D K I⟩ : QuadraticIdeal)) cols a M

def maskedPoissonDifference {n : Type} [Fintype n]
    (D : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily (quadraticMaskIdeal D) cols a W M - (Nat.card Oˣ : ℂ)⁻¹ *
    maskedPrincipalSourceSum (quadraticMaskIdeal D) (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K =>
        (⟨I.val, coprimeSquarefreeIdealBall_admissible D K I⟩ : QuadraticIdeal)) cols a M

lemma finite_centering_identity {ι : Type*} (S : Finset ι) (w R D : ι → ℂ) (c h : ℂ) :
    (∑ q∈S, w q*(c*R q-h*D q)) = c*(∑ q∈S,w q*R q)-h*(∑ q∈S,w q*D q) := by
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem maskedPoissonDifference_centered {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) 
    (hray : ∀ j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k))
    (hGc : ∀ j, IsCoprime (quadraticMaskIdeal D) (cols j).val) :
    (Nat.card Oˣ : ℂ)*maskedPoissonDifference D W cols a M K =
      (∑ q∈idealDivisors (quadraticMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
      (Nat.card Oˣ : ℂ)*maskedDualTailFamily (quadraticMaskIdeal D) cols a W M K - centeredMaskedSource D W cols a M K +
      paperRadialFourier (quadraticSquareProfile W) 0 *
        ((Real.sqrt M:ℂ)*principalDifference cols (densityColumn cols a) D K) := by
  rw [←source_dual_density_cancellation cols a D M K hM.le hray hGc]
  unfold maskedPoissonDifference centeredRetainedDual centeredMaskedSource divisorTwist
  rw [maskedDualFamily_retained (quadraticMaskIdeal D) (quadraticMaskIdeal_squarefree D).ne_zero cols a W M K hM hray]
  simp only [quadraticSquareProfile_principal_equal]
  rw [finite_centering_identity]
  simp only [mul_sub,mul_add,←mul_assoc,mul_inv_cancel₀ eisenstein_unit_card_ne_zero,one_mul]
  ring

theorem maskedPoissonDifference_norm_le {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) 
    (hray : ∀ j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k))
    (hGc : ∀ j, IsCoprime (quadraticMaskIdeal D) (cols j).val) :
    ‖(Nat.card Oˣ : ℂ)*maskedPoissonDifference D W cols a M K‖ ≤
      (∑ q∈idealDivisors (quadraticMaskIdeal D), ‖centeredRetainedDual W cols a M K q‖) +
      (Nat.card Oˣ : ℝ)*‖maskedDualTailFamily (quadraticMaskIdeal D) cols a W M K‖ + ‖centeredMaskedSource D W cols a M K‖ +
      ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
        ‖(Real.sqrt M:ℂ)*principalDifference cols (densityColumn cols a) D K‖ := by
  rw [maskedPoissonDifference_centered D W cols a M K hM hray hGc]
  have hs : ‖∑ q∈idealDivisors (quadraticMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ ≤
      ∑ q∈idealDivisors (quadraticMaskIdeal D), ‖centeredRetainedDual W cols a M K q‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one q)
  calc
    _ ≤ (‖∑ q∈idealDivisors (quadraticMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ +
        ‖(Nat.card Oˣ : ℂ)*maskedDualTailFamily (quadraticMaskIdeal D) cols a W M K‖) + ‖centeredMaskedSource D W cols a M K‖ +
        ‖paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*principalDifference cols (densityColumn cols a) D K)‖ := by
      have h1 := norm_add_le
        ((∑ q∈idealDivisors (quadraticMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (Nat.card Oˣ : ℂ)*maskedDualTailFamily (quadraticMaskIdeal D) cols a W M K - centeredMaskedSource D W cols a M K)
        (paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*principalDifference cols (densityColumn cols a) D K))
      have h2 := norm_sub_le
        ((∑ q∈idealDivisors (quadraticMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (Nat.card Oˣ : ℂ)*maskedDualTailFamily (quadraticMaskIdeal D) cols a W M K) (centeredMaskedSource D W cols a M K)
      have h3 := norm_add_le
        (∑ q∈idealDivisors (quadraticMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q)
        ((Nat.card Oˣ : ℂ)*maskedDualTailFamily (quadraticMaskIdeal D) cols a W M K)
      linarith
    _ ≤ _ := by
      simp only [norm_mul, Complex.norm_natCast]
      gcongr
theorem divisorTwist_norm_le {n : Type} (cols : n → QuadraticIdeal) (a : n → ℂ)
    (q : Ideal O) (j : n) : ‖divisorTwist cols a q j‖≤‖a j‖ := by
  rw [divisorTwist,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)

theorem retainedDualMajorant_coefficient_scale_le {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a a' : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0<N) (hM : 0≤M) (hF : 1≤F) (hT : 0≤T)
    (ha : ∀j, ‖a' j‖≤‖a j‖) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a' W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M 1 T a W := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' a a' ha ha
  have he0 := divisorEnergyFactor_nonneg ε hε N a' a'
  have he1 := divisorEnergyFactor_nonneg ε hε N a a
  have hea : (∑j, ‖a' j‖^2)≤∑j, ‖a j‖^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
  have hs := (divisorConstant_pos ε hε).le
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have hF0 : 0<F := by linarith
  have hMF : M/F≤M := div_le_self hM hF
  have hNF : N≤F*N := by nlinarith
  have hMN : 2*M/(F*N)≤2*M/N :=
    div_le_div_of_nonneg_left (by positivity) hN hNF
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  simp only [div_one,one_mul]
  gcongr

theorem centeredRetainedDual_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → QuadraticIdeal), Function.Injective cols →
        (∀j, N/2≤(Ideal.absNorm (cols j).val:ℝ) ∧ (Ideal.absNorm (cols j).val:ℝ)≤N) →
        (∀j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_global l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT cols hc hcols hray a W
  classical
  have hqbound (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖centeredRetainedDual W cols a M K q‖ ≤
        (columnDyadicLength K+1:ℕ)*
          retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
    have hqd := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqd; exact hG hqd
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hh := hbound hexp hα deltaLoss hδ ε hε K N M (Ideal.absNorm q:ℝ) T hK hN hM
      (by linarith) hT cols hc hcols hray (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact retainedDualMajorant_coefficient_scale_le s C hC.le l hexp deltaLoss hδ ε hε
      (2*K) N M (Ideal.absNorm q:ℝ) T a (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
      (by linarith) (by linarith) hM.le hq1 (by linarith) (divisorTwist_norm_le cols a q)
  calc
    _ ≤ ∑_q∈idealDivisors G, (columnDyadicLength K+1:ℕ)*
        retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) :=
      Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  (Nat.card Oˣ : ℝ)*((2*diagonalControl sieveCutoff)*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(divisorConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)


/-- All retained, tail, source, and boundary terms satisfy one centered Poisson estimate. -/
theorem HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε) (D : Ideal O)
        (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → QuadraticIdeal), Function.Injective cols →
        (∀ j, N/2≤(Ideal.absNorm (cols j).val:ℝ) ∧ (Ideal.absNorm (cols j).val:ℝ)≤N) →
        (∀ j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k)) →
        (∀ j, IsCoprime (quadraticMaskIdeal D) (cols j).val) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(Nat.card Oˣ : ℂ)*maskedPoissonDifference D W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
            (quadraticMaskIdeal D) K N M T a W := by
  obtain ⟨sD,CD,hCD,hdual⟩ := centeredRetainedDual_sum_bound l
  obtain ⟨sS,CS,hCS,hsource⟩ := masked_source_principal_global l
  obtain ⟨sT,CT,hCT,htail⟩ := maskedDualTailFamily_bound A
  obtain ⟨CP,hCP,hprincipal⟩ := hexp.principal_difference deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro n _ _ ε hε D K N M T hK hN hM hT cols hc hcols hray hGc a W hW
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hG := quadraticMaskIdeal_squarefree D
  have hcolsu : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N := fun j => (hcols j).2
  have hd := hdual hexp hα deltaLoss hδ ε hε (quadraticMaskIdeal D) hG.ne_zero K N M T
    hK hN hM0 hT cols hc hcols hray a W
  have hs := hsource hexp hα deltaLoss hδ ε hε (quadraticMaskIdeal D) hG K N M T hK hN hM0 hT
    (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K)
    (fun I hI => ⟨coprimeSquarefreeIdealBall_admissible D K ⟨I,hI⟩,
      (mem_squarefreeIdealBall.mp (Finset.mem_filter.mp hI).1).2⟩)
    cols hc hcolsu hGc a (quadraticSquareProfile W)
    (by simpa only [quadraticSquareProfile_apply,zero_pow (by decide : 2≠0)] using hW)
  have ht := htail (quadraticMaskIdeal D) cols a W M N K hG.ne_zero hc hM0 hN (by linarith) hcols
  have hp := hprincipal cols hc M N K hM hN hK hcolsu hray
    (densityColumn cols a) D ε hε
  have he := densityColumn_energy_le cols a
  have hsupp := (divisorConstant_pos ε hε).le
  have hp' : ‖(Real.sqrt M:ℂ)*principalDifference cols (densityColumn cols a) D K‖ ≤
      ((idealDivisors (quadraticMaskIdeal D)).card:ℝ)^2*(divisorConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑ j, ‖a j‖^2 := by
    apply hp.trans
    gcongr
  have hmain := maskedPoissonDifference_norm_le D W cols a M K hM0 hray hGc
  apply hmain.trans
  change _ ≤ _+_+_+_
  have hs' : ‖centeredMaskedSource D W cols a M K‖ ≤
      (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε
        (quadraticMaskIdeal D) (2*K) N M T a (quadraticSquareProfile W) := hs
  exact add_le_add (add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))) hs')
    (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson UniqueFactorizationMonoid
open scoped SchwartzMap

lemma primaryIdealPair_norm_sq (I J : QuadraticIdeal) :
    ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ ^ 2 =
      (Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ) := by
  rw [ringComplex_norm_sq_eq_absNorm_span, ← Ideal.span_singleton_mul_span_singleton,
    (primaryIdealGenerator_spec I.val I.property.1).1,
    (primaryIdealGenerator_spec J.val J.property.1).1, map_mul, Nat.cast_mul]

lemma primaryIdealPair_norm (I J : QuadraticIdeal) :
    ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ =
      Real.sqrt ((Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ)) := by
  rw [← primaryIdealPair_norm_sq I J, Real.sqrt_sq (norm_nonneg _)]

def maskedPairIdealSourceKernel (G : Ideal O) (I J : QuadraticIdeal) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ∑' H : NonzeroIdeal,
    primeCoprimeMask cubicIdealGenerator (primeSupport G) (cubicIdealGenerator H.val) *
      canonicalQuadraticPairIdeal I J H.val * W ((Ideal.absNorm H.val : ℝ) / M)

/-- Same-ray quadratic reciprocity and lattice Poisson give the ideal divisor expansion. -/
theorem maskedPairIdealSourceKernel_poisson (G : Ideal O) (hG : Squarefree G)
    (I J : QuadraticIdeal) (hcop : IsCoprime I.val J.val)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (hnt : I.val ≠ 1 ∨ J.val ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    maskedPairIdealSourceKernel G I J W M = maskedPairIdealDualKernel G I J W M := by
  let P := fun P : primeSupport G => P.val
  letI : ∀ P : primeSupport G, P.val.IsMaximal := fun P =>
    (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero
  have hprime (Q : primeSupport G) : Prime (P Q) := support_prime Q.property
  have hm (z : O) : primeCoprimeMask (fun Q : primeSupport G => cubicIdealGenerator Q.val) Finset.univ z =
      primeCoprimeMask cubicIdealGenerator (primeSupport G) z := by
    simp only [primeCoprimeMask]
    exact Finset.prod_coe_sort (s := primeSupport G)
      (f := fun Q : Ideal O => (1 : ℂ) - if cubicIdealGenerator Q ∣ z then 1 else 0)
  have hp := canonical_same_ray_pair_ideal_poisson I J hcop hray hnt
    (fun Q : primeSupport G => cubicIdealGenerator Q.val)
    (fun Q => cubicIdealGenerator_ne_zero Q.val (support_prime Q.property).ne_zero)
    (generator_pairwise_coprime P Subtype.val_injective) Finset.univ W M hM
  simp_rw [hm] at hp
  change maskedPairIdealSourceKernel G I J W M = _ at hp
  rw [primaryIdealPair_norm I J] at hp
  have hsq : (Real.sqrt ((Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ)))^2 =
      (Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ) := Real.sq_sqrt (by positivity)
  simp_rw [hsq] at hp
  rw [hp, maskedPairIdealDualKernel]
  congr 1
  rw [← primeSupport_subset_sum_eq_divisors G hG (fun d =>
    ((moebius d : ℂ) * canonicalQuadraticPairIdeal I J d / (Ideal.absNorm d : ℂ)) *
      ∑' H : NonzeroIdeal, canonicalQuadraticPairIdeal I J H.val * paperRadialFourier W
        ((M / ((Ideal.absNorm d : ℝ) * (Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ))) *
          (Ideal.absNorm H.val : ℝ)))]
  apply Finset.sum_congr rfl
  intro E hE
  have hn := primeSubsetGenerator_norm_sq P E
  have hs := primeSubsetGenerator_span P E
  simp only [primeSubsetGenerator, P] at hn hs
  rw [hn, hs, prime_product_moebius P hprime Subtype.val_injective E]
  simp only [Complex.ofReal_natCast]
  congr 1
  apply tsum_congr
  intro H
  congr 2
  ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy IdealCoprimeBilinearSieve FiniteSieveRestriction

/-- A bounded row weight in one exact common-conductor block. -/
def weightedCommonFactorBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → O) (cols : n → QuadraticIdeal) (w : m → ℂ) (a : n → ℂ) : ℂ :=
  ∑ i, w i * ∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D then
    star (canonicalQuadraticRow (cols j) (rows i) * a j) *
      (canonicalQuadraticRow (cols k) (rows i) * a k) else 0

theorem highKernel_weightedCommonFactorBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε) (D : QuadraticIdeal)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    ‖weightedCommonFactorBlock D.val (fun i => primaryIdealGenerator (rows i).val) cols w a‖ ≤
      W * highKernelNorm M (N / Ideal.absNorm D.val) K * (divisorConstant ε hε * N ^ ε) *
        ∑ j, ‖if D.val ∣ (cols j).val then a j else 0‖ ^ 2 := by
  classical
  have hD0 := primaryIdealGenerator_ne_zero_ideal D.val D.property.1
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D.val := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hdiv : N / Ideal.absNorm D.val ≤ N := by
    exact div_le_self hN0 hDN
  let S : Finset n := Finset.univ.filter (fun j => D.val ∣ (cols j).val)
  have hS (j : S) : D.val ∣ (cols j.val).val := (Finset.mem_filter.mp j.property).2
  let q : S → QuadraticIdeal := fun j => ⟨quadraticIdealQuotient D.val (cols j.val).val,
    quadraticIdealQuotient_admissible (cols j.val).property (hS j)⟩
  have hq : Function.Injective q := by
    intro i j he
    apply Subtype.ext
    apply hc
    apply Subtype.ext
    apply quadraticIdealQuotient_injective D.val (hS i) (hS j)
    exact congrArg (fun I : QuadraticIdeal => I.val) he
  have hqn (j : S) : (Ideal.absNorm (q j).val : ℝ) ≤ N / Ideal.absNorm D.val := by
    change (Ideal.absNorm (quadraticIdealQuotient D.val (cols j.val).val) : ℝ) ≤ _
    rw [quadraticIdealQuotient_norm hD0 (hS j)]
    exact div_le_div_of_nonneg_right (hcols j.val) (Nat.cast_nonneg _)
  let A : Matrix m S ℂ := fun i j => canonicalQuadraticRow (q j) (primaryIdealGenerator (rows i).val)
  let v (i : m) : ℂ := canonicalQuadraticRow D (primaryIdealGenerator (rows i).val)
  let T (i : m) (j k : n) : ℂ := if (cols j).val ⊔ (cols k).val = D.val then
    star (canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) * a j) *
      (canonicalQuadraticRow (cols k) (primaryIdealGenerator (rows i).val) * a k) else 0
  have hzero_left (i : m) (j k : n) (hj : j ∉ S) : T i j k = 0 := by
    apply if_neg
    intro he
    apply hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Ideal.dvd_iff_le.mpr (he ▸ (le_sup_left : (cols j).val ≤ (cols j).val ⊔ (cols k).val))⟩
  have hzero_right (i : m) (j k : n) (hk : k ∉ S) : T i j k = 0 := by
    apply if_neg
    intro he
    apply hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Ideal.dvd_iff_le.mpr (he ▸ (le_sup_right : (cols k).val ≤ (cols j).val ⊔ (cols k).val))⟩
  have heq (i : m) : (∑ j, ∑ k, T i j k) =
      star (v i) * v i *
        (∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
          star (A i j * a j.val) * (A i k * a k.val) else 0) := by
    calc
      _ = ∑ j ∈ S, ∑ k ∈ S, T i j k := by
        have hj : (∑ j, ∑ k, T i j k) = ∑ j ∈ S, ∑ k, T i j k := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro j _ hj
          exact Finset.sum_eq_zero (fun k _ => hzero_left i j k hj)
        rw [hj]
        apply Finset.sum_congr rfl
        intro j _
        symm
        exact Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => hzero_right i j k hk)
      _ = ∑ j : S, ∑ k : S, T i j.val k.val := by
        rw [Finset.sum_coe_sort (s := S) (f := fun j => ∑ k : S, T i j k.val)]
        exact Finset.sum_congr rfl (fun j _ =>
          (Finset.sum_coe_sort (s := S) (f := fun k => T i j k)).symm)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        have hiff := quadraticIdealQuotient_coprime_iff D.val (cols j.val).val (cols k.val).val
          hD0 (hS j) (hS k)
        change (if (cols j.val).val ⊔ (cols k.val).val = D.val then _ else 0) = _
        by_cases h : (q j).val ⊔ (q k).val = ⊤
        · rw [if_pos (hiff.mp h), if_pos h]
          rw [canonicalQuadraticRow_divisor_factor (cols j.val) D.val (hS j),
            canonicalQuadraticRow_divisor_factor (cols k.val) D.val (hS k), star_mul, star_mul]
          change (star (a j.val) * (star (A i j) * star (v i))) * (v i * A i k * a k.val) = _
          simp only [star_mul]
          ring
        · rw [if_neg (fun hc => h (hiff.mpr hc)), if_neg h, mul_zero]
  have hn : ‖weightedCommonFactorBlock D.val (fun i => primaryIdealGenerator (rows i).val) cols w a‖ ≤
      W * ∑ i, ‖∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
        star (A i j * a j.val) * (A i k * a k.val) else 0‖ := by
    change ‖∑ i, w i * ∑ j, ∑ k, T i j k‖ ≤ _
    simp_rw [heq]
    rw [Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    have hv : ‖v i‖ * ‖v i‖ ≤ 1 :=
      (mul_le_mul (canonicalQuadraticRow_norm_le_one D _) (canonicalQuadraticRow_norm_le_one D _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    calc
      _ ≤ W * (1 * ‖∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
          star (A i j * a j.val) * (A i k * a k.val) else 0‖) :=
        mul_le_mul (hw i) (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) (by positivity) hW
      _ = _ := by rw [one_mul]
  have hb := ideal_coprime_bilinear_operator_bound ε hε
    (fun j : S => (q j).val) (fun j : S => (q j).val)
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (q j).property.1)
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (q j).property.1)
    N N (fun j => (hqn j).trans hdiv) (fun j => (hqn j).trans hdiv)
    A A (fun j : S => a j.val) (fun j : S => a j.val)
  have hL : 0 ≤ divisorConstant ε hε * N ^ ε :=
    mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hop := highKernel_family_squared_norm_le rows q hr hq M (N / Ideal.absNorm D.val) K hrows hqn hK
  have hs : (∑ j : S, ‖a j.val‖ ^ 2) = ∑ j, ‖if D.val ∣ (cols j).val then a j else 0‖ ^ 2 := by
    rw [Finset.sum_coe_sort (s := S) (f := fun j : n => ‖a j‖ ^ 2)]
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hb' := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (mul_nonneg (sq_nonneg _) hL) (by positivity))).mp
      (show (∑ i, ‖∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
        star (A i j * a j.val) * (A i k * a k.val) else 0‖) ^ 2 ≤
        (‖FiniteSieveOperator.operator A‖ ^ 2 * (divisorConstant ε hε * N ^ ε) * ∑ j : S, ‖a j.val‖ ^ 2) ^ 2 by
          simpa only [pow_two] using hb)
  apply hn.trans
  calc
    _ ≤ W * (‖FiniteSieveOperator.operator A‖ ^ 2 * (divisorConstant ε hε * N ^ ε) * ∑ j : S, ‖a j.val‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb' hW
    _ ≤ W * (highKernelNorm M (N / Ideal.absNorm D.val) K * (divisorConstant ε hε * N ^ ε) * ∑ j : S, ‖a j.val‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hop hL) (by positivity)) hW
    _ = _ := by rw [hs]; ring


theorem highKernel_large_weightedCommonFactorBlocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (S : Finset (Ideal O)) (hS : S ⊆ commonFactorPool cols) (G : ℝ) (hG : 0 < G)
    (hSG : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    (∑ D ∈ S, ‖weightedCommonFactorBlock D (fun i => primaryIdealGenerator (rows i).val) cols w a‖) ≤
      W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hL : 0 ≤ divisorConstant ε hε * N ^ ε :=
    mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg (zero_le_one.trans hN) _)
  have hb (D : Ideal O) (hD : D ∈ S) :
      ‖weightedCommonFactorBlock D (fun i => primaryIdealGenerator (rows i).val) cols w a‖ ≤
      W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2 := by
    have hh := highKernel_weightedCommonFactorBlock_bound ε hε
      ⟨D, commonFactorPool_admissible cols D (hS hD)⟩ rows cols hr hc M N K hN hrows hcols hK w W hW hw a
    have hm := highKernelNorm_mono (M := M) (M' := M) (K := K) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (zero_le_one.trans hN) hG (hSG D hD)) le_rfl
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hW) hL) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        (∑ D ∈ S, ∑ j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2) := (Finset.mul_sum ..).symm
    _ ≤ W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (divisor_mask_energy_small_power ε hε S
        (fun j => (cols j).val) (fun j => primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1)
        N hcols a) (mul_nonneg (mul_nonneg hW (highKernelNorm_nonneg _ _ _)) hL)
    _ = _ := by ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy FiniteSieveRestriction
open scoped Classical

lemma weighted_energy_eq_commonFactorBlocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → O) (cols : n → QuadraticIdeal) (v : m → ℝ) (a : n → ℂ) :
    ((∑ i, v i * ‖∑ j, canonicalQuadraticRow (cols j) (rows i) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ commonFactorPool cols, weightedCommonFactorBlock D rows cols (fun i => (v i : ℂ)) a := by
  have hi (i : m) : ((‖∑ j, canonicalQuadraticRow (cols j) (rows i) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ commonFactorPool cols, ∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D then
        star (canonicalQuadraticRow (cols j) (rows i) * a j) *
          (canonicalQuadraticRow (cols k) (rows i) * a k) else 0 := by
    simpa only [commonFactorBlock, Fintype.sum_unique] using
      energy_eq_commonFactorBlocks (fun _ : Unit => rows i) cols a
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hi, Finset.mul_sum, weightedCommonFactorBlock]
  rw [Finset.sum_comm]

lemma weighted_energy_le_commonFactorBlocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → O) (cols : n → QuadraticIdeal) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, canonicalQuadraticRow (cols j) (rows i) * a j‖ ^ 2) ≤
      ∑ D ∈ commonFactorPool cols, ‖weightedCommonFactorBlock D rows cols (fun i => (v i : ℂ)) a‖ := by
  have he := congrArg norm (weighted_energy_eq_commonFactorBlocks rows cols v a)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_weighted_energy_commonFactor_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (G : ℝ) (hG : 0 < G) (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ))
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) * a j‖ ^ 2) ≤
      (∑ D ∈ (commonFactorPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        ‖weightedCommonFactorBlock D (fun i => primaryIdealGenerator (rows i).val) cols (fun i => (v i : ℂ)) a‖) +
      W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := weighted_energy_le_commonFactorBlocks (fun i => primaryIdealGenerator (rows i).val) cols v (fun i => (hv i).1) a
  rw [← Finset.sum_filter_add_sum_filter_not (commonFactorPool cols)
    (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_weightedCommonFactorBlocks ε hε rows cols hr hc _
    (Finset.filter_subset _ _) G hG (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    M N K hN hrows hcols hK (fun i => (v i : ℂ)) W hW
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv i).1] using (hv i).2) a))

def weightedRayCommonFactorBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : QuadraticRayRing) (rows : m → O) (cols : n → QuadraticIdeal)
    (v : m → ℝ) (a : n → ℂ) : ℂ :=
  weightedCommonFactorBlock D rows cols (fun i => (v i : ℂ))
    (sectorCoefficient (fun j => quadraticColumnRay (cols j)) c a)

/-- Ray separation leaves a small-conductor Poisson sum and a shorter high-kernel remainder. -/
theorem highKernel_weighted_energy_ray_commonFactor_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (G : ℝ) (hG : 0 < G) (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ))
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) * a j‖ ^ 2) ≤
      16 * ((∑ c : QuadraticRayRing,
        ∑ D ∈ (commonFactorPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖weightedRayCommonFactorBlock D c (fun i => primaryIdealGenerator (rows i).val) cols v a‖) +
        W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → QuadraticRayRing := fun j => quadraticColumnRay (cols j)
  let C := W * highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) ^ 2
  have hs := weighted_energy_sector_bound σ
    (fun i j => canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val)) a v (fun i => (hv i).1)
  rw [quadraticRayRing_card] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : QuadraticRayRing,
        ((∑ D ∈ (commonFactorPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖weightedRayCommonFactorBlock D c (fun i => primaryIdealGenerator (rows i).val) cols v a‖) +
            C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_weighted_energy_commonFactor_reduction ε hε rows cols hr hc G hG M N K hN
        hrows hcols hK v W hW hv (sectorCoefficient σ c a)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap ContDiff Classical

/-- Smooth annular majorant, equal to one on the half-to-one shell. -/
def annularSieveBump : ContDiffBump (3 / 4 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def annularSieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    annularSieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annularSieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem annularSieveCutoff_apply (t : ℝ) : annularSieveCutoff t = (annularSieveBump t : ℂ) := rfl

theorem annularSieveBump_eq_one {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) : annularSieveBump t = 1 := by
  apply annularSieveBump.one_of_mem_closedBall
  change dist t (3 / 4) ≤ 1 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

theorem annularSieveBump_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem annularSieveBump_zero_of_ge {t : ℝ} (ht : 5 / 4 ≤ t) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

@[simp] theorem annularSieveCutoff_zero : annularSieveCutoff 0 = 0 := by
  rw [annularSieveCutoff_apply, annularSieveBump_zero_of_le (by norm_num), Complex.ofReal_zero]


/-- Supported ideals with a squarefree part larger than the chosen cutoff. -/
def highKernelRange (M K : ℝ) : Finset (Ideal O) :=
  (Finset.univ.image (fun I : QuadraticSupportedRange M => I.val.val)).filter
    (fun I => K < (Ideal.absNorm (quadraticSquarefreePart I) : ℝ))

lemma mem_highKernelRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelRange M K ↔ quadraticSupported I ∧ (Ideal.absNorm I : ℝ) ≤ M ∧
      K < (Ideal.absNorm (quadraticSquarefreePart I) : ℝ) := by
  constructor
  · intro h
    obtain ⟨hi,hk⟩ := Finset.mem_filter.mp h
    obtain ⟨J,_,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨J.val.property,J.property,hk⟩
  · rintro ⟨hs,hn,hk⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨⟨I,hs⟩,hn⟩,Finset.mem_univ _,rfl⟩,hk⟩

def annularHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  annularSieveBump ((Ideal.absNorm I : ℝ) / M)

def annularHighEnergy (M N K : ℝ) (a : QuadraticIdealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2*M) K, annularHighWeight M I.val *
    ‖∑ J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val) * a J‖ ^ 2

def annularRayCommonFactorBlock (M N K : ℝ) (D : Ideal O) (c : QuadraticRayRing)
    (a : QuadraticIdealRange N → ℂ) : ℂ :=
  weightedRayCommonFactorBlock D c (fun I : highKernelRange (2*M) K => primaryIdealGenerator I.val)
    (fun J : QuadraticIdealRange N => J.val) (fun I => annularHighWeight M I.val) a

theorem annularHighEnergy_commonFactor_reduction (M N K G : ℝ)
    (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) (a : QuadraticIdealRange N → ℂ) :
    annularHighEnergy M N K a ≤ 16 *
      ((∑ c : QuadraticRayRing,
        ∑ D ∈ (commonFactorPool (fun J : QuadraticIdealRange N => J.val)).filter
          (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖annularRayCommonFactorBlock M N K D c a‖) +
        highKernelNorm (2*M) (N/G) K * (DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2 * ∑ J, ‖a J‖^2) := by
  let rows : highKernelRange (2*M) K → QuadraticSupportedIdeal :=
    fun I => ⟨I.val,(mem_highKernelRange.mp I.property).1⟩
  have hr : Function.Injective rows := by
    intro I J h
    exact Subtype.ext (congrArg (fun Q : QuadraticSupportedIdeal => Q.val) h)
  have h := highKernel_weighted_energy_ray_commonFactor_reduction ε hε rows
    (fun J : QuadraticIdealRange N => J.val) hr Subtype.val_injective G hG (2*M) N K hN
    (fun I => (mem_highKernelRange.mp I.property).2.1) (fun J => J.property)
    (fun I => (mem_highKernelRange.mp I.property).2.2)
    (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨annularSieveBump.nonneg, annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy,annularRayCommonFactorBlock,rows,one_mul] using h

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein UniqueFactorizationMonoid

/-- Multiplication by even powers of this prime moves rows into a fixed annulus. -/
def liftingPrime : Ideal O := CubicRamified.sevenIdeal

lemma liftingPrime_norm : Ideal.absNorm liftingPrime = 7 := CubicRamified.sevenIdeal_norm

lemma liftingPrime_prime : Prime liftingPrime := by
  apply Ideal.prime_of_isPrime
  · intro h
    have hn := Ideal.absNorm_eq_zero_iff.mpr h
    rw [liftingPrime_norm] at hn
    norm_num at hn
  · exact inferInstanceAs CubicRamified.sevenIdeal.IsPrime

lemma liftingPrime_odd : ringChar (O ⧸ liftingPrime) ≠ 2 := by
  letI : Finite (O ⧸ liftingPrime) := finite_quotient_span CubicRamified.sevenPrime_ne_zero
  letI : Fintype (O ⧸ liftingPrime) := Fintype.ofFinite _
  have hcard : Fintype.card (O ⧸ liftingPrime) = 7 := by
    rw [← Nat.card_eq_fintype_card]
    exact CubicRamified.sevenIdeal_card
  intro h
  have hd : ringChar (O ⧸ liftingPrime) ∣ Fintype.card (O ⧸ liftingPrime) :=
    ringChar.dvd (Nat.cast_card_eq_zero (R := O ⧸ liftingPrime))
  rw [h,hcard] at hd
  norm_num at hd

lemma liftingPrime_supported : quadraticSupported liftingPrime := by
  refine ⟨?_,?_⟩
  · change primaryIdealGenerator (Ideal.span {CubicRamified.sevenPrime}) ≠ 0
    rw [primaryIdealGenerator_span _ CubicRamified.sevenPrime_ne_zero CubicRamified.sevenPrime_primary]
    exact CubicRamified.sevenPrime_ne_zero
  · intro P hP
    have hp := support_prime hP
    letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hd : P ∣ liftingPrime := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
    have he : CubicRamified.sevenIdeal = P := Ideal.IsMaximal.eq_of_le
      (inferInstance : CubicRamified.sevenIdeal.IsMaximal)
      (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) (Ideal.dvd_iff_le.mp hd)
    rw [← he]
    exact liftingPrime_odd

lemma liftingPrime_admissible : quadraticIdealAdmissible liftingPrime :=
  ⟨liftingPrime_supported.1,liftingPrime_prime.squarefree,liftingPrime_supported.2⟩

lemma quadraticSupported_pow {I : Ideal O} (hI : quadraticSupported I) (k : ℕ) :
    quadraticSupported (I ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    refine ⟨?_,?_⟩
    · change primaryIdealGeneratorHom 1 ≠ 0
      rw [map_one]
      exact one_ne_zero
    · intro P hP
      simp only [primeSupport,normalizedFactors_one,Multiset.toFinset_zero,Finset.notMem_empty] at hP
  | succ k hk =>
    rw [pow_succ]
    exact (quadraticSupported_mul _ _).mpr ⟨hk,hI⟩

lemma exists_lifting_exponent (M : ℝ) (I : Ideal O) (hI : I ≠ 0)
    (hIM : (Ideal.absNorm I : ℝ) ≤ M) :
    ∃ k : ℕ, M < (49 : ℝ)^k * (Ideal.absNorm I : ℝ) ∧
      (49 : ℝ)^k * (Ideal.absNorm I : ℝ) ≤ 49*M := by
  have hN : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hN).mpr (by simpa using hIM))
    (by norm_num : (1 : ℝ) < 49)
  refine ⟨k+1,?_,?_⟩
  · exact (div_lt_iff₀ hN).mp hhi
  · have h := (le_div_iff₀ hN).mp hlo
    rw [pow_succ]
    nlinarith only [h]

def liftingExponent (M : ℝ) (I : Ideal O) (hI : I ≠ 0) (hIM : (Ideal.absNorm I : ℝ) ≤ M) : ℕ :=
  (exists_lifting_exponent M I hI hIM).choose

def liftedRow (M : ℝ) (I : Ideal O) (hI : I ≠ 0) (hIM : (Ideal.absNorm I : ℝ) ≤ M) : Ideal O :=
  I * (liftingPrime ^ liftingExponent M I hI hIM)^2

lemma liftedRow_norm (M : ℝ) (I : Ideal O) (hI : I ≠ 0) (hIM : (Ideal.absNorm I : ℝ) ≤ M) :
    (Ideal.absNorm (liftedRow M I hI hIM) : ℝ) =
      (49 : ℝ)^liftingExponent M I hI hIM * (Ideal.absNorm I : ℝ) := by
  simp only [liftedRow,map_mul,map_pow,liftingPrime_norm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num <;> ring

lemma liftedRow_bounds (M : ℝ) (I : Ideal O) (hI : I ≠ 0) (hIM : (Ideal.absNorm I : ℝ) ≤ M) :
    M < (Ideal.absNorm (liftedRow M I hI hIM) : ℝ) ∧
      (Ideal.absNorm (liftedRow M I hI hIM) : ℝ) ≤ 49*M := by
  rw [liftedRow_norm]
  exact (exists_lifting_exponent M I hI hIM).choose_spec

lemma liftedRow_squarefreePart (M : ℝ) (I : Ideal O) (hI : quadraticIdealAdmissible I)
    (hIM : (Ideal.absNorm I : ℝ) ≤ M) :
    quadraticSquarefreePart (liftedRow M I (primaryIdealGenerator_ne_zero_ideal I hI.1) hIM) = I :=
  (quadraticParts_of_squarefree I _ hI.2.1 (pow_ne_zero _ liftingPrime_prime.ne_zero)).1

lemma liftedRow_supported (M : ℝ) (I : Ideal O) (hI : quadraticIdealAdmissible I)
    (hIM : (Ideal.absNorm I : ℝ) ≤ M) :
    quadraticSupported (liftedRow M I (primaryIdealGenerator_ne_zero_ideal I hI.1) hIM) :=
  (quadraticSupported_mul _ _).mpr
    ⟨⟨hI.1,hI.2.2⟩,quadraticSupported_pow (quadraticSupported_pow liftingPrime_supported _) 2⟩

/-- An even prime power leaves quadratic characters unchanged on coprime columns. -/
lemma liftedRow_character (M : ℝ) (I : Ideal O) (hI : quadraticIdealAdmissible I)
    (hIM : (Ideal.absNorm I : ℝ) ≤ M) (J : QuadraticIdeal) (hPJ : IsCoprime liftingPrime J.val) :
    canonicalQuadraticRow J (primaryIdealGenerator (liftedRow M I (primaryIdealGenerator_ne_zero_ideal I hI.1) hIM)) =
      canonicalQuadraticRow J (primaryIdealGenerator I) := by
  rw [liftedRow,canonicalQuadraticRow_squarefree_argument,quadraticIdealMask_indicator,
    (primaryIdealGenerator_spec _ (quadraticSupported_pow liftingPrime_supported _).1).1,
    if_pos hPJ.pow_left,mul_one]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy
open scoped Classical

def squarefreeHighRange (M K : ℝ) : Finset (QuadraticIdealRange M) :=
  Finset.univ.filter (fun I => K < (Ideal.absNorm I.val.val : ℝ))

def annularLift (M K : ℝ) (I : squarefreeHighRange M K) : Ideal O :=
  liftedRow M I.val.val.val (primaryIdealGenerator_ne_zero_ideal _ I.val.val.property.1) I.val.property

theorem annularLift_injective (M K : ℝ) : Function.Injective (annularLift M K) := by
  intro I J h
  have he := congrArg quadraticSquarefreePart h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simpa only [annularLift,liftedRow_squarefreePart M I.val.val.val I.val.val.property,
    liftedRow_squarefreePart M J.val.val.val J.val.val.property] using he

theorem annularLift_properties (M K : ℝ) (I : squarefreeHighRange M K) :
    quadraticSupported (annularLift M K I) ∧
      K < (Ideal.absNorm (quadraticSquarefreePart (annularLift M K I)) : ℝ) ∧
      M < (Ideal.absNorm (annularLift M K I) : ℝ) ∧ (Ideal.absNorm (annularLift M K I) : ℝ) ≤ 49*M := by
  have hn := liftedRow_bounds M I.val.val.val
    (primaryIdealGenerator_ne_zero_ideal _ I.val.val.property.1) I.val.property
  refine ⟨liftedRow_supported M I.val.val.val I.val.val.property I.val.property,?_,hn⟩
  simpa only [annularLift,liftedRow_squarefreePart M I.val.val.val I.val.val.property] using
    (Finset.mem_filter.mp I.property).2

theorem annularLift_row_sum (M N K : ℝ) (I : squarefreeHighRange M K)
    (a : QuadraticIdealRange N → ℂ)
    (hcop : ∀ J, a J ≠ 0 → IsCoprime liftingPrime J.val.val) :
    (∑ J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator (annularLift M K I))*a J) =
      ∑ J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*a J := by
  apply Finset.sum_congr rfl
  intro J _
  by_cases hz : a J=0
  · simp only [hz,mul_zero]
  · rw [annularLift,liftedRow_character M I.val.val.val I.val.val.property I.val.property J.val (hcop J hz)]

lemma exists_lifted_annular_scale (M x : ℝ) (hM : 0<M) (hx : M<x) (hupper : x≤49*M) :
    ∃j : Fin 7, ((2:ℝ)^j.val*M)/2≤x ∧ x≤(2:ℝ)^j.val*M := by
  have hratio : 1≤x/M := (le_div_iff₀ hM).mpr (by linarith)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hratioU : x/M≤49 := (div_le_iff₀ hM).mpr hupper
  have hk : k<6 := by
    by_contra hn
    have h6 : 6≤k := by omega
    have hp : (2:ℝ)^6≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) h6
    norm_num at hp
    linarith
  refine ⟨⟨k+1,by omega⟩,?_,?_⟩
  · have hl := (le_div_iff₀ hM).mp hlo
    simpa only [pow_succ,mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hl
  · exact ((div_lt_iff₀ hM).mp hhi).le

lemma sum_injective_mask_le {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (hf : Function.Injective f) (S : Finset (Ideal O))
    (v : Ideal O → ℝ) (hv : ∀I, 0≤v I) :
    (∑i, if f i∈S then v (f i) else 0)≤∑I∈S,v I := by
  classical
  rw [←Finset.sum_filter]
  rw [←Finset.sum_image (f := v) (g := f) (by intro i hi j hj he; exact hf he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hi).2
  · intro I hI hnot
    exact hv I

theorem squarefreeHigh_energy_le_annuli (M N K : ℝ) (hM : 0<M)
    (a : QuadraticIdealRange N → ℂ) (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val.val) :
    (∑I : squarefreeHighRange M K,
      ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*a J‖^2) ≤
      ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K a := by
  classical
  let E := fun I : Ideal O => ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I)*a J‖^2
  have hE (I : Ideal O) : 0≤E I := sq_nonneg _
  have hlift :
      (∑I : squarefreeHighRange M K, E I.val.val.val) = ∑I : squarefreeHighRange M K, E (annularLift M K I) := by
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [E]
    rw [annularLift_row_sum M N K I a hcop]
  change (∑I : squarefreeHighRange M K, E I.val.val.val)≤_
  rw [hlift]
  have hpoint (I : squarefreeHighRange M K) : E (annularLift M K I) ≤
      ∑j : Fin 7, if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := by
    have hp := annularLift_properties M K I
    obtain ⟨j,hjlo,hjhi⟩ := exists_lifted_annular_scale M _ hM hp.2.2.1 hp.2.2.2
    have hMj : 0<(2:ℝ)^j.val*M := by positivity
    have hm : annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K :=
      mem_highKernelRange.mpr ⟨hp.1,by linarith,hp.2.1⟩
    have hw : annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)=1 := by
      apply annularSieveBump_eq_one
      · exact (le_div_iff₀ hMj).mpr (by linarith)
      · exact (div_le_one hMj).mpr hjhi
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0)
      (fun j _ => by split_ifs; exact mul_nonneg annularSieveBump.nonneg (hE _); exact le_rfl)
      (Finset.mem_univ j)
    simpa only [hm,ite_true,hw,one_mul] using hh
  calc
    _ ≤ ∑I : squarefreeHighRange M K, ∑j : Fin 7,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑j : Fin 7, ∑I : squarefreeHighRange M K,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [annularHighEnergy,Finset.sum_coe_sort (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)]
      exact sum_injective_mask_le (annularLift M K) (annularLift_injective M K)
        (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)
        (fun I => mul_nonneg annularSieveBump.nonneg (hE I))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
