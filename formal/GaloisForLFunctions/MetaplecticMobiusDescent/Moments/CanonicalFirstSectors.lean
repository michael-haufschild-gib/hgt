/-
Canonical first sectors adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.ActiveSupports
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PrimePowerGaussSums

/-!
# Canonical first sectors

Left and right exponents, common indices and active conductors of the canonical first stage;
first nominal scales, residual pools and the fixed first sums of sector energies.
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
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstMixed
open Eisenstein  CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => Eisenstein.O

theorem frequencyReduction_comp (d n M : O) (hd : d∣n) (hn : n∣M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x)=frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [frequencyReduction_mk]

theorem three_factor_mixed_fourier (a b c : O) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b*c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b*c))] [Fintype (Residue (a*(b*c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a*(b*c))) :
    (∑ x : Residue (a*(b*c)),
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
      χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
      G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)*
        primitiveTrace (a*(b*c)) (mul_ne_zero ha (mul_ne_zero hb hc)) (h*x)) =
      χa (Ideal.Quotient.mk _ (b*c))*χb (Ideal.Quotient.mk _ (a*c))*
        residueGauss a ha χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) h)*
        residueGauss b hb χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h)*
        (∑ y : Residue c,G (Ideal.Quotient.mk _ (a*b)*y)*
          primitiveTrace c hc (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h*y)) := by
  let F : Residue (b*c) → ℂ := fun y =>
    χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
      G (frequencyReduction c (b*c) (dvd_mul_left _ _) y)
  let h' := frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) h
  have he (x : Residue (a*(b*c))) :
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        F (frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) x) =
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
        G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp,frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [ProbePhysical.coprime_mixed_fourier a (b*c) ha (mul_ne_zero hb hc) habc χa F h]
  have hf (y : Residue (b*c)) : F (Ideal.Quotient.mk _ a*y)=
      χb (Ideal.Quotient.mk _ a)*
        (χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
          G (Ideal.Quotient.mk _ a*frequencyReduction c (b*c) (dvd_mul_left _ _) y)) := by
    simp only [F,map_mul,frequencyReduction_mk]
    ring
  simp_rw [hf,mul_assoc]
  rw [← Finset.mul_sum]
  have hh := ProbePhysical.coprime_mixed_fourier b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a*y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h',frequencyReduction_comp,map_mul,mul_assoc]
  ring

end CenteredMomentFirstMixed

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstReduced
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentActive
local notation "O" => Eisenstein.O

def tripleRow (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) : ℂ :=
  χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*G (Ideal.Quotient.mk _ z)

def tripleResidue (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (x : Residue (a*(b*r))) : ℂ :=
  χa (frequencyReduction a _ (dvd_mul_right _ _) x)*
    χb (frequencyReduction b _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
    G (frequencyReduction r _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)

@[simp] theorem tripleResidue_mk (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) :
    tripleResidue a b r χa χb G (Ideal.Quotient.mk _ z)=tripleRow a b r χa χb G z := by
  simp only [tripleResidue,tripleRow,frequencyReduction_mk]

theorem tripleRow_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y,G (x*y)=G x*G y) (x y : O) :
    tripleRow a b r χa χb G (x*y)=tripleRow a b r χa χb G x*tripleRow a b r χa χb G y := by
  simp only [tripleRow,map_mul,hG]
  ring

def tripleFourier (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (h : O) : ℂ :=
  ∑' x : Residue (a*(b*r)),tripleResidue a b r χa χb G x*
    primitiveTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)

theorem tripleRow_radial_summable (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z : O => tripleRow a b r χa χb G z*W (‖ringComplex z‖^2/K)) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a*(b*r)})) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,scaledRadialTest_apply] using hh

theorem tripleRow_poisson (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    (∑' z : O,tripleRow a b r χa χb G z*W (‖ringComplex z‖^2/K)) =
      ((K/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W (K*‖ringComplex h‖^2/‖ringComplex (a*(b*r))‖^2) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_radial_poisson_trace W K hK (a*(b*r))
    (mul_ne_zero ha (mul_ne_zero hb hr)) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,tripleFourier,primitiveTrace,tsum_fintype,Complex.real_smul] using hh

theorem masked_triple_poisson {α : Type*} (P : α → Ideal O)
    [∀ i,(P i).IsMaximal] (hinj : Function.Injective P) (S : Finset α)
    (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x y,G (x*y)=G x*G y)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    (∑' z : O,rowCoprimeMask P S z*tripleRow a b r χa χb G z*W (‖ringComplex z‖^2/K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖ringComplex e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb hr χa χb G h*
              paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (a*(b*r))‖^2)) := by
  rw [tsum_masked_radial_dilations P hinj S _ (tripleRow_mul a b r χa χb G hG) W K
    (tripleRow_radial_summable a b r ha hb hr χa χb G W K hK)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [tripleRow_poisson a b r ha hb hr χa χb G W _ (primeSubset_reducedScale_pos P E hK)]

theorem principalSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,lambda ∉ P i)
    (j : ι → ℕ) (r : O) (hr : Ideal.span {r}=∏ i,P i) (x y : Residue r) :
    principalSexticRow P hcop hg j r hr (x*y)=
      principalSexticRow P hcop hg j r hr x*principalSexticRow P hcop hg j r hr y := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul,principalSexticRow_mk P hcop hg j r hr (x*y),
    principalSexticRow_mk P hcop hg j r hr x,principalSexticRow_mk P hcop hg j r hr y,
    finiteSexticRow_mul P hg j x y]

theorem common_residual_reduced_poisson {ι : Type*}
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i,lambda ∉ P i) (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (B : Finset ι) (c d : ι → ℕ) (hc : ∀ i∈B,c i≠0) (hd : ∀ i∈B,d i≠0)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    let Q := fun i : activeSupport B c d => P i.val
    let hj := fun i : activeSupport B c d => netExponent (c i.val) (d i.val)
    let r := finitePrimeModulus Q
    let G := principalSexticRow Q (activePrimes_pairwise_coprime P hinj B c d)
      (fun i => hg i.val) hj r (span_finitePrimeModulus Q)
    (∑' z : O,χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*
      (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^c i)*
        star (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^d i)))*
      W (‖ringComplex z‖^2/K)) =
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖ringComplex e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i∈E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb (finitePrimeModulus_ne_zero Q) χa χb G h*
              paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (a*(b*r))‖^2)) := by
  dsimp only
  rw [← masked_triple_poisson P hinj (principalSupport B c d) a b _ ha hb
    (finitePrimeModulus_ne_zero _) χa χb _
    (principalSexticRow_mul _ _ _ _ _ _) W K hK]
  apply tsum_congr
  intro z
  rw [common_ideal_pair_active P hg hchar B c d hc hd]
  simp only [tripleRow,principalSexticRow_mk (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => netExponent (c i.val) (d i.val)) _ (span_finitePrimeModulus _) z]
  ring

end CenteredMomentFirstReduced

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstActiveFourier
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentFirstReduced
local notation "O" => Eisenstein.O

theorem shifted_active_fourier {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6) (v h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      primitiveTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finiteEisensteinQuotientOfNonzero (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  change finiteSexticRow P hg j v*(star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j)=_
  ring

theorem tripleFourier_active {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finiteEisensteinQuotientOfNonzero ha
  let := finiteEisensteinQuotientOfNonzero hb
  let := finiteEisensteinQuotientOfNonzero (finitePrimeModulus_ne_zero P)
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]

theorem tripleFourier_active_norm_le {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    ‖tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h‖ ≤
      ‖ringComplex r‖*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖ := by
  dsimp only
  let := finiteEisensteinQuotientOfNonzero ha
  let := finiteEisensteinQuotientOfNonzero hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b ha hb har hbr]
  simp only [norm_mul,norm_star,norm_canonicalGaussSum P hcop hg hchar j hj0 hj6]
  have hχa := FiniteRayExpansion.norm_char_le_one χa (Ideal.Quotient.mk _ (b*finitePrimeModulus P))
  have hχb := FiniteRayExpansion.norm_char_le_one χb (Ideal.Quotient.mk _ (a*finitePrimeModulus P))
  have hv := SchwartzPlanePoisson.finiteSexticRow_norm_le_one P hg j (a*b)
  have hh := SchwartzPlanePoisson.finiteSexticRow_norm_le_one P hg j h
  calc
    _ ≤ 1*1*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
      ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖*(1*1*‖ringComplex (finitePrimeModulus P)‖) := by
        gcongr
    _ = _ := by ring

end CenteredMomentFirstActiveFourier

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentCanonicalFirst
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentFirstActiveFourier CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

abbrev CommonIndex (I J : Ideal O) := {P : Ideal O // P∈commonSupport I J}
instance commonIndexMaximal (I J : Ideal O) (P : CommonIndex I J) : P.val.IsMaximal := by
  have hp := prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

def leftExponent (I J : Ideal O) (P : CommonIndex I J) := valuation I P.val
def rightExponent (I J : Ideal O) (P : CommonIndex I J) := valuation J P.val

theorem common_good (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    lambda ∉ P.val :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.1

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

theorem leftExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< leftExponent I J P :=
  (common_valuations_pos I J P.val P.property).1

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

theorem commonPart_left_product (I J : Ideal O) :
    commonPart I J=∏ P : CommonIndex I J,P.val^leftExponent I J P := by
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation I P)).symm

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

abbrev ActiveIndex (I J : Ideal O) :=
  activeSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)
def activePrime (I J : Ideal O) (P : ActiveIndex I J) : Ideal O := P.val.val
instance activePrimeMaximal (I J : Ideal O) (P : ActiveIndex I J) : (activePrime I J P).IsMaximal :=
  commonIndexMaximal I J P.val

def activeConductor (I J : Ideal O) : O := finitePrimeModulus (activePrime I J)
def activeExponent (I J : Ideal O) (P : ActiveIndex I J) :=
  netExponent (leftExponent I J P.val) (rightExponent I J P.val)
theorem activeGood (I J : Ideal O) (hI : Supported I) (P : ActiveIndex I J) :
    lambda ∉ activePrime I J P := common_good I J hI P.val

theorem activeCoprime (I J : Ideal O) : Pairwise (Function.onFun IsCoprime (activePrime I J)) :=
  activePrimes_pairwise_coprime (fun P : CommonIndex I J => P.val) Subtype.val_injective
    Finset.univ (leftExponent I J) (rightExponent I J)

def activeFunction (I J : Ideal O) (hI : Supported I) : Residue (activeConductor I J) → ℂ :=
  principalSexticRow (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (activeExponent I J) (activeConductor I J) (span_finitePrimeModulus _)

def residualGenerator (I J : Ideal O) : O := primaryIdealGenerator (residualPart I J)

theorem residualGenerator_span (I J : Ideal O) (hI : Supported I) :
    Ideal.span {residualGenerator I J}=residualPart I J :=
  (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ (residualPart_supported I J hI))).1

theorem residualGenerator_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {residualGenerator I J}) := by
  rw [residualGenerator_span I J hI]
  exact residualPart_supported I J hI

def residualCharacter (I J : Ideal O) (hI : Supported I) : MulChar (Residue (residualGenerator I J)) ℂ :=
  supportedModulusCharacter _ (residualGenerator_supported I J hI)

@[simp] theorem residualCharacter_mk (I J : Ideal O) (hI : Supported I) (z : O) :
    residualCharacter I J hI (Ideal.Quotient.mk _ z)=idealRowHom z (residualPart I J) := by
  rw [residualCharacter,supportedModulusCharacter_mk,residualGenerator_span I J hI]

theorem original_pair_factor (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (z : O) :
    idealRowHom z I*star (idealRowHom z J)=
      residualCharacter I J hI (Ideal.Quotient.mk _ z)*
        (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z)*
        (idealRowHom z (∏ P : CommonIndex I J,P.val^leftExponent I J P)*
          star (idealRowHom z (∏ P : CommonIndex I J,P.val^rightExponent I J P))) := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
  rw [← MulChar.star_apply',residualCharacter_mk,residualCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product]
  have hi := congrArg (idealRowHom z) (reconstruct I J hI.1)
  have hj := congrArg (idealRowHom z) (reconstruct J I hJ.1)
  simp only [map_mul] at hi hj
  rw [hi,hj,star_mul]
  ring

def reducedFirstSum (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let k := K/‖ringComplex e‖^2
    let a := residualGenerator I J
    let b := residualGenerator J I
    let r := activeConductor I J
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
      (((k/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
          paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (a*(b*r))‖^2))

theorem canonical_pair_reduced_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    (∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖ringComplex z‖^2/K))=
      reducedFirstSum I J hI hJ W K := by
  simp_rw [original_pair_factor I J hI hJ]
  exact common_residual_reduced_poisson (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (common_good I J hI) (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => ne_of_gt (leftExponent_pos I J P)) (fun P _ => ne_of_gt (rightExponent_pos I J P))
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ W K hK

theorem activeConductor_span_dvd (I J : Ideal O) :
    Ideal.span {activeConductor I J} ∣ commonPart I J := by
  rw [activeConductor,span_finitePrimeModulus]
  change (∏ P : ActiveIndex I J,P.val.val) ∣ commonPart I J
  rw [Finset.prod_coe_sort]
  refine (Finset.prod_dvd_prod_of_subset _ Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem residual_active_coprime (I J : Ideal O) (hI : Supported I) :
    IsCoprime (residualGenerator I J) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI]
  exact (commonPart_own_residual_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)

theorem opposite_residual_active_coprime (I J : Ideal O) (hJ : Supported J) :
    IsCoprime (residualGenerator J I) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span J I hJ]
  exact (commonPart_residualPart_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)

theorem residual_generators_coprime (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    IsCoprime (residualGenerator I J) (residualGenerator J I) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI,residualGenerator_span J I hJ]
  exact residualParts_coprime I J

theorem canonical_tripleFourier_norm_le (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (h : O) :
    ‖tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h‖ ≤
      ‖ringComplex (activeConductor I J)‖*
        ‖residueGauss (residualGenerator I J) (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (residualCharacter I J hI) (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss (residualGenerator J I) (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
          (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)‖ := by
  exact tripleFourier_active_norm_le (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (fun P => common_odd I J hI P.val) (activeExponent I J)
    (netExponent_ne_zero _ _ _) (fun P => netExponent_lt_six _ _)
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    ((residual_generators_coprime I J hI hJ).mul_right (residual_active_coprime I J hI))
    (opposite_residual_active_coprime I J hJ) _ _ h

end CenteredMomentCanonicalFirst

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def firstNominalScale (I J E : Ideal O) (K X : ℝ) : ℝ :=
  (Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*X^2 /
    (K*(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (commonPart J I):ℝ))

theorem norm_pos (I : Ideal O) (hI : I≠0) : 0<(Ideal.absNorm I:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem active_norm_pos (I J : Ideal O) :
    0<(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ) := by
  apply norm_pos
  exact Ideal.span_singleton_eq_bot.not.mpr (SchwartzPlanePoisson.finitePrimeModulus_ne_zero _)

theorem firstNominalScale_pos (I J E : Ideal O) (hE : E≠0) (K X : ℝ)
    (hK : 0< K) (hX : 0< X) : 0< firstNominalScale I J E K X := by
  unfold firstNominalScale
  exact div_pos (mul_pos (mul_pos (norm_pos E hE) (active_norm_pos I J)) (sq_pos_of_pos hX))
    (mul_pos (mul_pos hK (norm_pos _ (commonPart_ne_zero I J))) (norm_pos _ (commonPart_ne_zero J I)))

theorem first_kernel_ratio (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H : ℝ) (hK : 0< K) (hX : 0< X) :
    K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
      (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) =
      (H/firstNominalScale I J E K X)*(X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) := by
  have hc := norm_pos _ (commonPart_ne_zero I J)
  have hd := norm_pos _ (commonPart_ne_zero J I)
  have he := norm_pos E hE
  have hr := active_norm_pos I J
  have ha := norm_pos _ (residualPart_ne_zero I J)
  have hb := norm_pos _ (residualPart_ne_zero J I)
  have hi : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (residualPart I J):ℝ) := by
    exact_mod_cast absNorm_reconstruct I J hI
  have hj : (Ideal.absNorm J:ℝ)=(Ideal.absNorm (commonPart J I):ℝ)*(Ideal.absNorm (residualPart J I):ℝ) := by
    exact_mod_cast absNorm_reconstruct J I hJ
  rw [hi,hj]
  unfold firstNominalScale
  field_simp

theorem first_kernel_lower (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H HN : ℝ) (hK : 0< K) (hX : 0< X) (hH : 0≤ H)
    (hi : (Ideal.absNorm I:ℝ)≤ Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤ Real.exp HN*X) :
    H/(Real.exp (2*HN)*firstNominalScale I J E K X) ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  rw [first_kernel_ratio I J E hI hJ hE K X H hK hX]
  have hnI := norm_pos I hI
  have hnJ := norm_pos J hJ
  have hT := firstNominalScale_pos I J E hE K X hK hX
  have hh : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤ Real.exp (2*HN)*X^2 := by
    calc
      _ ≤ (Real.exp HN*X)*(Real.exp HN*X) := mul_le_mul hi hj hnJ.le (by positivity)
      _ = _ := by rw [show 2*HN=HN+HN by ring,Real.exp_add];ring
  have hr : 1/Real.exp (2*HN) ≤ X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
    apply (div_le_div_iff₀ (Real.exp_pos _) (mul_pos hnI hnJ)).mpr
    simpa only [one_mul,mul_comm] using hh
  calc
    _ = (H/firstNominalScale I J E K X)*(1/Real.exp (2*HN)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (div_nonneg hH hT.le)

theorem first_kernel_sector_lower (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H HN Tsec : ℝ) (hK : 0< K) (hX : 0< X) (hH : 0≤ H)
    (hi : (Ideal.absNorm I:ℝ)≤ Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤ Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤ Tsec) :
    (Real.exp (-2*HN)/Tsec)*H ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  have hT := firstNominalScale_pos I J E hE K X hK hX
  calc
    _ = H/(Real.exp (2*HN)*Tsec) := by rw [show -2*HN=-(2*HN) by ring,Real.exp_neg];ring
    _ ≤ H/(Real.exp (2*HN)*firstNominalScale I J E K X) :=
      div_le_div_of_nonneg_left hH (mul_pos (Real.exp_pos _) hT)
        (mul_le_mul_of_nonneg_left hsec (Real.exp_pos _).le)
    _ ≤ _ := first_kernel_lower I J E hI hJ hE K X H HN hK hX hH hi hj

end CenteredMomentFirstScale

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstDiscarded
open CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open Eisenstein  SchwartzPlanePoisson
local notation "O" => Eisenstein.O

theorem actual_first_kernel_reference (I J E : Ideal O)
    (hI : I≠0) (hJ : J≠0) (hE : E≠0) (K X HN Tsec : ℝ)
    (hK : 0< K) (hX : 0< X)
    (hi : (Ideal.absNorm I:ℝ)≤ Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤ Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤ Tsec) :
    kernelReference Tsec HN ≤
      K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  simpa only [kernelReference,mul_one] using
    first_kernel_sector_lower I J E hI hJ hE K X 1 HN Tsec hK hX zero_le_one hi hj hsec

theorem canonical_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0< C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J E : Ideal O) (hI : Supported I) (hJ : Supported J), E≠0 →
      ∀ K X HN Tsec Z Csec ξ : ℝ, 0< K → 0< X → 1< Z → 1≤ Csec →
      (Ideal.absNorm I:ℝ)≤ Real.exp HN*X → (Ideal.absNorm J:ℝ)≤ Real.exp HN*X →
      firstNominalScale I J E K X≤ Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W
          ((K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
            (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)))*normValue h)‖ ≤
      (‖ringComplex (activeConductor I J)‖*(Ideal.absNorm (residualPart I J):ℝ)*
        (Ideal.absNorm (residualPart J I):ℝ))*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W I J E hI hJ hE K X HN Tsec Z Csec ξ hK hX hZ hCsec hi hj hsec hthreshold
  have hT : 0< Tsec := (firstNominalScale_pos I J E hE K X hK hX).trans_le hsec
  apply ht W Tsec Z Csec HN ξ _ _ hT hZ hCsec hthreshold
    (actual_first_kernel_reference I J E hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec)
    (by positivity)
  intro h
  apply (canonical_tripleFourier_norm_le I J hI hJ h).trans
  have ha := CenteredMomentTail.residueGauss_norm_le (residualGenerator I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (residualCharacter I J hI) (Ideal.Quotient.mk _ h)
  have hb := CenteredMomentTail.residueGauss_norm_le (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)
  have ha' := ha.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span I J hI))
  have hb' := hb.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span J I hJ))
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha' (norm_nonneg _)) hb' (norm_nonneg _) (by positivity)

end CenteredMomentFirstDiscarded

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstDiscardedEnergy
open Eisenstein  CubicEisenstein SchwartzPlanePoisson 
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon 
local notation "O" => Eisenstein.O

theorem tripleRow_norm_le_one (a b r : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (z : O) :
    ‖tripleRow a b r χa χb G z‖≤1 := by
  let := finiteEisensteinQuotientOfNonzero ha
  let := finiteEisensteinQuotientOfNonzero hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleRow,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one χa _)).trans
      (FiniteRayExpansion.norm_char_le_one χb _))).trans (hG _)

theorem tripleFourier_norm_le_full (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (h : O) :
    ‖tripleFourier a b r ha hb hr χa χb G h‖≤ normValue (a*(b*r)) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  rw [tripleFourier,tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a*(b*r)),‖tripleResidue a b r χa χb G x*
      CenteredMomentFourier.primitiveTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a*(b*r)),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [norm_mul,(CenteredMomentFourier.primitiveTrace _ _).norm_apply,mul_one,tripleResidue_mk]
      exact tripleRow_norm_le_one a b r ha hb χa χb G hG z
    _ = _ := by simp [normValue,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem activeFunction_norm_le_one (I J : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (x : Residue (activeConductor I J)) : ‖activeFunction I J hI x‖≤1 := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    _ = ‖finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z‖ :=
      congrArg norm (principalSexticRow_mk (activePrime I J) (activeCoprime I J)
        (activeGood I J hI) (CenteredMomentCanonicalFirst.activeExponent I J)
        (activeConductor I J) (span_finitePrimeModulus _) z)
    _ ≤ 1 := SchwartzPlanePoisson.finiteSexticRow_norm_le_one _ _ _ z

theorem scaled_discarded_triple_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0< C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ k : ℝ),
      0< Tsec → 1< Z → 1≤ Csec → 0< k →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ∀ (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
        (G : Residue r → ℂ), (∀ x,‖G x‖≤1) →
      kernelReference Tsec H≤ k/normValue (a*(b*r)) →
      ‖((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
        (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h)‖ ≤
      k*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ k hT hZ hCs hk hthreshold a b r ha hb hr χa χb G hG hscale
  have hN : 0< normValue (a*(b*r)) := norm_pos _
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr)))
  have hh := ht W Tsec Z Csec H ξ (k/normValue (a*(b*r))) (normValue (a*(b*r)))
    hT hZ hCs hthreshold hscale hN.le (tripleFourier a b r ha hb hr χa χb G)
    (tripleFourier_norm_le_full a b r ha hb hr χa χb G hG)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hk hN)]
  apply (mul_le_mul_of_nonneg_left hh (div_pos hk hN).le).trans_eq
  field_simp

def canonicalDiscardedTerm (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem canonical_kernel_scale (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (K : ℝ) :
    (K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/
      normValue (residualGenerator I J*(residualGenerator J I*activeConductor I J)) =
      K/((Ideal.absNorm (∏ P∈E,P.val):ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart I J):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart J I):ℝ)) := by
  rw [normValue_mul,normValue_mul]
  unfold normValue
  rw [TruncatedPrincipalPoisson.primeSubsetGenerator_span,residualGenerator_span I J hI,residualGenerator_span J I hJ,div_div]
  congr 1
  ring

theorem canonical_discarded_term_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0< C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (E : Finset (CommonIndex I J)) (K X HN Tsec Z Csec ξ : ℝ),
      0< K → 0< X → 1< Z → 1≤ Csec →
      (Ideal.absNorm I:ℝ)≤ Real.exp HN*X → (Ideal.absNorm J:ℝ)≤ Real.exp HN*X →
      firstNominalScale I J (∏ P∈E,P.val) K X≤ Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ ≤
      K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := scaled_discarded_triple_bound A
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hE : (∏ P∈E,P.val)≠(0:Ideal O) := by
    have hh := Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [e,TruncatedPrincipalPoisson.primeSubsetGenerator_span,Ideal.zero_eq_bot] using hh
  have hNe : 0< normValue e := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)
  have hNe1 : 1≤ normValue e := by
    change (1:ℝ)≤(Ideal.absNorm (Ideal.span {e}):ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr he))
  have hk := div_pos hK hNe
  have hkK : K/normValue e≤ K := div_le_self hK.le hNe1
  have hT := (firstNominalScale_pos I J _ hE K X hK hX).trans_le hsec
  have hscale := actual_first_kernel_reference I J _ hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec
  rw [← canonical_kernel_scale I J hI hJ E K] at hscale
  have hb := ht W Tsec Z Csec HN ξ (K/normValue e) hT hZ hCs hk hthreshold
    (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
    (activeFunction_norm_le_one I J hI) hscale
  have hm : ‖(UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e‖≤1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (IdealCoprimeBilinearSieve.moebius_norm_le_one _)).trans
      (tripleRow_norm_le_one _ _ _ (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) _ _ _ (activeFunction_norm_le_one I J hI) e)
  change ‖_ * _‖≤ _
  rw [norm_mul]
  apply (mul_le_mul hm hb (norm_nonneg _) zero_le_one).trans
  rw [one_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkK (by positivity)) (by positivity)

def inactiveSubsets (I J : Ideal O) : Finset (Finset (CommonIndex I J)) :=
  (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset

theorem inactiveSubsets_card (I J : Ideal O) :
    (inactiveSubsets I J).card≤2^(primeSupport I).card := by
  rw [inactiveSubsets,Finset.card_powerset]
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    _ ≤ (Finset.univ : Finset (CommonIndex I J)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = (commonSupport I J).card := by simp [CommonIndex]
    _ ≤ _ := Finset.card_le_card Finset.inter_subset_left

def canonicalDiscardedPair (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ

theorem canonical_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0< C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0< K → 0< X → 1< Z → 1≤ Csec →
      (Ideal.absNorm I:ℝ)≤ Real.exp HN*X → (Ideal.absNorm J:ℝ)≤ Real.exp HN*X →
      (∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤ Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedPair I J hI hJ W K Tsec Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤ D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => ht W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec E hE) hthreshold)
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end CenteredMomentFirstDiscardedEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstTailAggregate
open Eisenstein HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => Eisenstein.O

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0< C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O))
        (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0< K → 0< X → 1< Z → 1≤ Csec →
      (∀ I∈S,(Ideal.absNorm I:ℝ)≤ Real.exp HN*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,∀ E∈inactiveSubsets I J,
        firstNominalScale I J (∏ P∈E,P.val) K X≤ Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖ ≤
      (∑ I∈S,‖c I‖)^2*(Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X HN Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤ B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤ B := by
    have hi := hN I (Finset.mem_filter.mp I.property).1
    have hj := hN J (Finset.mem_filter.mp J.property).1
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec I J) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hi hε.le) hK.le
  have hcoeff (I : supportedColumns S) : ‖c I*rowWeight η m A 1 t I‖≤‖c I‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1)
  have hmass : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  have he : (∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B)=
      (∑ I : supportedColumns S,‖c I‖)^2*B := by
    rw [pow_two,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.mul_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ I : supportedColumns S,‖∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B := by
      apply Finset.sum_le_sum
      intro I hI
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (hcoeff I) (hcoeff J) (norm_nonneg _) (norm_nonneg _))
        (hpair I J) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ I : supportedColumns S,‖c I‖)^2*B := he
    _ ≤ (∑ I∈S,‖c I‖)^2*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass 2) hB
    _ = _ := by dsimp only [B];ring

end CenteredMomentFirstTailAggregate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical

namespace CenteredMomentPrimaryCharacter
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimary CenteredMomentCommonSupport
local notation "O" => Eisenstein.O

def rawPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ where
  toFun n := primaryIdealCharacter r χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton,map_mul]

def maskedPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ :=
  coprimalityMask (3:O)*rawPrimaryHom r χ

theorem maskedPrimaryHom_unit_mul (r : O) (χ : MulChar (Residue r) ℂ) (u : Oˣ) (n : O) :
    maskedPrimaryHom r χ ((u:O)*n)=maskedPrimaryHom r χ n := by
  change (if IsCoprime (3:O) ((u:O)*n) then (1:ℂ) else 0)*
      primaryIdealCharacter r χ (Ideal.span {(u:O)*n}) =
    (if IsCoprime (3:O) n then (1:ℂ) else 0)*primaryIdealCharacter r χ (Ideal.span {n})
  rw [isCoprime_mul_unit_left_right u.isUnit,Ideal.span_singleton_mul_left_unit u.isUnit]

theorem maskedPrimaryHom_ramified (r : O) (χ : MulChar (Residue r) ℂ) (n : O) (hn : lambda∣n) :
    maskedPrimaryHom r χ n=0 := by
  have h3 : lambda∣(3:O) := (dvd_pow_self lambda (by decide : 2≠0)).trans Eisenstein.lambda_sq_dvd_three
  have hc : ¬IsCoprime (3:O) n := fun hc =>
    residue_lambda_prime.not_unit (hc.isUnit_of_dvd' h3 hn)
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*_=0
  rw [if_neg hc,zero_mul]

theorem maskedPrimaryHom_primary (r : O) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : lambda^2∣n-1) : maskedPrimaryHom r χ n=χ (Ideal.Quotient.mk _ n) := by
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*
    χ (Ideal.Quotient.mk _ (primaryIdealGenerator (Ideal.span {n})))=_
  rw [if_pos (CubicEisenstein.primary_coprime_three n hn).symm,one_mul,
    primaryIdealGenerator_span n (Eisenstein.primary_ne_zero n hn) hn]

theorem maskedPrimaryHom_periodic (r : O) (χ : MulChar (Residue r) ℂ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {3*r}) (maskedPrimaryHom r χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom
  apply periodic_of_primary _ _ _ F _ (maskedPrimaryHom_unit_mul r χ)
    (maskedPrimaryHom_ramified r χ) (maskedPrimaryHom_primary r χ)
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact Eisenstein.lambda_sq_dvd_three.trans (dvd_mul_right _ _)
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_left r 3).trans (Ideal.mem_span_singleton.mp hxy))

def primaryCharacter (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) : Character :=
  rowCharacter (Ideal.span {3*r})
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hr))
    (maskedPrimaryHom r χ) (maskedPrimaryHom_periodic r χ)
    (fun u => by simpa only [mul_one,map_one] using maskedPrimaryHom_unit_mul r χ u 1)

@[simp] theorem primaryCharacter_modulus (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus=Ideal.span {3*r} := rfl

theorem primaryCharacter_primary (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : lambda^2∣n-1) : elementCoeff (primaryCharacter r hr χ) n=χ (Ideal.Quotient.mk _ n) := by
  rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_primary r χ n hn]
  split_ifs with hc
  · rfl
  · symm
    apply MulChar.map_nonunit
    intro hu
    apply hc
    apply isUnit_residue_of_coprime
    apply (CubicEisenstein.primary_coprime_three n hn).symm.mul_left
    exact (CubicEisenstein.isUnit_quotient_span_iff r n).mp hu

theorem primaryCharacter_all (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O) :
    elementCoeff (primaryCharacter r hr χ) n=maskedPrimaryHom r χ n := by
  by_cases hn : lambda∣n
  · rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_ramified r χ n hn]
    split_ifs <;> rfl
  · have hg := (primaryIdealGenerator_span_ne_zero_iff n).mpr hn
    have hs := primaryIdealGenerator_spec (Ideal.span {n}) hg
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1.symm
    have hp : lambda^2∣(u:O)*n-1 := by
      have hp' : lambda^2∣primaryIdealGenerator (Ideal.span {n})-1 := hs.2
      rwa [mul_comm,hu]
    rw [← elementCoeff_unit_mul (primaryCharacter r hr χ) u n,
      ← maskedPrimaryHom_unit_mul r χ u n,primaryCharacter_primary r hr χ _ hp,
      maskedPrimaryHom_primary r χ _ hp]

theorem primaryCharacter_ideal (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (primaryCharacter r hr χ) I=
      χ (Ideal.Quotient.mk _ (primaryIdealGenerator I)) := by
  have hn := supported_primaryIdealGenerator_ne_zero I hI
  have hs := primaryIdealGenerator_spec I hn
  calc
    _ = elementCoeff (primaryCharacter r hr χ) (primaryIdealGenerator I) := by
      rw [← idealCoeff_span _ hn,hs.1]
    _ = _ := primaryCharacter_primary r hr χ _ hs.2

theorem primaryCharacter_modulus_norm (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus.absNorm=
      (Ideal.span {(3:O)}).absNorm*(Ideal.span {r}).absNorm := by
  rw [primaryCharacter_modulus,← Ideal.span_singleton_mul_span_singleton,map_mul]

end CenteredMomentPrimaryCharacter

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstNormalization
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CanonicalQuadraticSieve CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentSupportedCorrelation CenteredMomentFirstReduced CenteredMomentFirstActiveFourier
open CenteredMomentGaussEnergy CenteredMomentPrimitive CenteredMomentFirstPoisson
local notation "O" => Eisenstein.O

theorem residueGauss_eq_norm_mul_gaussRow (a : O) (ha : Supported (Ideal.span {a})) (h : O) :
    residueGauss a (supported_element_ne_zero a ha) (supportedModulusCharacter a ha) (Ideal.Quotient.mk _ h)=
      (‖ringComplex a‖:ℂ)*gaussRow a ha h := by
  have hn : (‖ringComplex a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero a ha)))
  rw [gaussRow,residueGauss_supported_mk,sqrt_absNorm]
  field_simp

theorem normalized_active_coefficient {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,lambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h /
      (‖ringComplex (a*(b*r))‖^2:ℝ) =
      (canonicalNormalizedGauss P hcop hg j /
        ((‖ringComplex a‖:ℂ)*(‖ringComplex b‖:ℂ)*(‖ringComplex r‖:ℂ)))*
      (CanonicalRowCompletion.idealRowHom (b*r) (Ideal.span {a})*
        star (CanonicalRowCompletion.idealRowHom (a*r) (Ideal.span {b}))*finiteSexticRow P hg j (a*b))*
      (star (finiteSexticRow P hg j h)*gaussRow a ha h*star (gaussRow b hb (-h))) := by
  dsimp only
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero b hb)
  have hna : (‖ringComplex a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero a ha)))
  have hnb : (‖ringComplex b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero b hb)))
  have hnr : (‖ringComplex (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero (finitePrimeModulus_ne_zero P)))
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb) har hbr,
    residueGauss_inverse,← map_neg,residueGauss_eq_norm_mul_gaussRow a ha,
    residueGauss_eq_norm_mul_gaussRow b hb,← MulChar.star_apply',
    supportedModulusCharacter_mk,supportedModulusCharacter_mk]
  simp only [canonicalNormalizedGauss,map_mul,norm_mul,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_mul]
  field_simp

end CenteredMomentFirstNormalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentChildAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentMobiusRegroup CenteredMomentRowNorm RayFourExpansion
local notation "O" => Eisenstein.O

def divisorCoefficient {α : Type*} (L : Ideal O) (a : α → O) (c : α → ℂ)
    (χ : RayCharacter) (i : α) : ℂ :=
  if L ∣ Ideal.span {a i} then c i * rayMonoid χ (a i) else 0

theorem rayCharacter_inverse_star (χ : RayCharacter) (a : O) :
    star (rayMonoid (χ⁻¹) a) = rayMonoid χ a := by
  change star ((χ⁻¹) (Ideal.Quotient.mk _ a)) = χ (Ideal.Quotient.mk _ a)
  rw [MulChar.star_apply', inv_inv]

theorem divisor_pair_separation {α β : Type*} (L : Ideal O) (a : α → O) (b : β → O)
    (c : α → ℂ) (d : β → ℂ) (D E h : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (i : α) (j : β) (K : ℂ) :
    (if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
      completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K else 0) =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
              star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K := by
  by_cases hi : L ∣ Ideal.span {a i}
  · by_cases hj : L ∣ Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [completeSupportExtension_separated D E h (a i) (b j) hD hE (ha i) (hb j)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,Finset.sum_const_zero,mul_zero]

theorem pair_ray_fubini {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (S : Finset α) (T : Finset β) (A : γ → δ → ℂ)
    (L : α → γ → ℂ) (R : β → δ → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, ∑ χ : γ, ∑ ξ : δ, A χ ξ * (L i χ * R j ξ) * K i j) =
      ∑ χ : γ, ∑ ξ : δ, A χ ξ * ∑ i ∈ S, ∑ j ∈ T, (L i χ * R j ξ) * K i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := S)]
  simp_rw [Finset.sum_comm (s := S) (t := Finset.univ)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem finite_correlation_children {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : lambda ^ 2 ∣ D - 1)
    (hpE : lambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, lambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, lambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) * actualCorrelation D E hD hE h *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable D E) χ ξ *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K i j := by
  rw [finite_correlation_mobius S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB h c d K]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [divisor_pair_separation L a b c d D E h hD hE ha hb]
  simp_rw [← Finset.mul_sum (s := T), ← Finset.mul_sum (s := S)]
  rw [pair_ray_fubini]
  ring

theorem separated_pair_rowPolynomials {α β : Type*} (S : Finset α) (T : Finset β)
    (L : Ideal O) (a : α → O) (b : β → O) (c : α → ℂ) (d : β → ℂ)
    (χ ξ : RayCharacter) (f : α → ℂ) (g : β → ℂ) (h : O) :
    (∑ i ∈ S, ∑ j ∈ T,
      ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
        star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) *
        (f i * star (g j))) =
      rowPolynomial S a (fun i => divisorCoefficient L a c χ i * f i) h *
        star (rowPolynomial T b (fun j => divisorCoefficient L b d (ξ⁻¹) j * g j) (-h)) := by
  simp only [rowPolynomial, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CenteredMomentChildAssembly

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstColumns
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => Eisenstein.O

def leftCoefficient (e r : O) (ρ : O → ℂ) (a : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {a})*ρ a

def rightCoefficient (e r : O) (ρ : O → ℂ) (b : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {b})*star (ρ b)

theorem first_phase_columns (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : lambda^2∣a-1)
    (hpb : lambda^2∣b-1) (hab : IsCoprime a b) :
    (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
      (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b)) =
      ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero a ha)
  let : Fintype (CenteredMomentCommonSupport.Residue a) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero b hb)
  let : Fintype (CenteredMomentCommonSupport.Residue b) := Fintype.ofFinite _
  have hp := supported_opposite_phase b a hb ha hpb hpa hab.symm
  rw [sexticReciprocityPhase_symm b a] at hp
  calc
    _ = ρ e*(idealRowHom b (Ideal.span {a})*star (idealRowHom a (Ideal.span {b})))*
        leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
      simp only [leftCoefficient,rightCoefficient,idealRowHom_argument_mul,hρ,star_mul,star_star]
      ring
    _ = _ := by rw [hp]

def firstPhaseTable (r s : RayRing) : ℂ := quotientPhase r s

theorem firstPhaseTable_mk (a b : O) :
    firstPhaseTable (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)=sexticReciprocityPhase a b :=
  quotientPhase_mk a b

theorem firstPhaseTable_expansion (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a b=∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*rayMonoid χ a*rayMonoid ξ b := by
  have hh := pair_phase_expansion firstPhaseTable a b
  simpa only [supported_rayMask a ha,supported_rayMask b hb,one_mul,firstPhaseTable_mk] using hh

theorem firstPhaseTable_mass :
    (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)≤256 := by
  have hb : ∀ u v : RayRingˣ,‖firstPhaseTable u v‖≤1 := by
    intro u v
    exact sexticReciprocityPhase_norm _ _
  simpa only [mul_one] using pairCoeff_sum_norm_le firstPhaseTable 1 hb

def firstExtension (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b)

theorem firstExtension_separated (e r a b : O) (ρ : O → ℂ)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    firstExtension e r ρ a b=ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*(leftCoefficient e r ρ a*rayMonoid χ a)*
        star (rightCoefficient e r ρ b*rayMonoid (ξ⁻¹) b) := by
  unfold firstExtension
  rw [firstPhaseTable_expansion a b ha hb]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul,CenteredMomentChildAssembly.rayCharacter_inverse_star]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  ring

end CenteredMomentFirstColumns

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped Classical

namespace CenteredMomentFirstFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimaryCharacter CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentCommonSupport RayFourExpansion
local notation "O" => Eisenstein.O

theorem exists_supported_row_presentation (η : Character) (m z : O)
    (hm : m≠0) (hz : Supported (Ideal.span {z})) (hmLam : lambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {z} ∧
      ∀ n : O,elementCoeff τ n=rowTwist (elementHom η) m 1 z n := by
  let r := primaryIdealGenerator (Ideal.span {z})
  have hr0 : r≠0 := supported_primaryIdealGenerator_ne_zero _ hz
  have hs := primaryIdealGenerator_spec (Ideal.span {z}) hr0
  have hr : Supported (Ideal.span {r}) := hs.1 ▸ hz
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1
  have hx : (1:O)^4*z=(u:O)*lambda^0*(2:O)^0*r := by
    simpa only [one_pow,pow_zero,mul_one,mul_comm] using hu.symm
  let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {r}
  have hM : M≠⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))) (Ideal.span_singleton_eq_bot.not.mpr hr0)
  have hG := rowTwist_periodic η m 1 z hmLam hm2 u 0 0 r hr hs.2 hx
  refine ⟨rowCharacter M hM (rowTwist (elementHom η) m 1 z) hG (rowTwist_unit η m 1 z),?_,?_⟩
  · change M=_
    dsimp only [M]
    rw [hs.1]
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m 1 z n hmLam hm2 u 0 0 r hx h)))

theorem first_period_contains (η : Character) (m e r : O) :
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    M≤ Ideal.span {3*r} ∧ M≤ Ideal.span {(12:O)} := by
  dsimp only
  constructor
  · calc
      _ ≤ Ideal.span {(72:O)}*Ideal.span {e*r} := by
        rw [mul_assoc]
        exact Ideal.mul_le_left
      _ = Ideal.span {(72:O)*(e*r)} := Ideal.span_singleton_mul_span_singleton _ _
      _ ≤ _ := Ideal.span_singleton_le_span_singleton.mpr ⟨24*e,by ring⟩
  · exact (Ideal.mul_le_right.trans Ideal.mul_le_left).trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)

theorem exists_first_character (η : Character) (m e r : O)
    (hm : m≠0) (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O,elementCoeff τ n=
        rowTwist (elementHom η) m 1 (e*r) n*maskedPrimaryHom r χ n*
          elementCoeff (primaryRayCharacter ξ) n) ∧
      ∀ n : O,Supported (Ideal.span {n}) → lambda^2∣n-1 →
        elementCoeff τ n=elementCoeff η n*coprimalityMask m n*
          idealRowHom (e*r) (Ideal.span {n})*χ (Ideal.Quotient.mk _ n)*rayMonoid ξ n := by
  obtain ⟨τ₀,hM,hτ⟩ := exists_supported_row_presentation η m (e*r) hm (supported_mul_elements e r he hr) hmLam hm2
  let τ := (τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ)
  have hp := first_period_contains η m e r
  refine ⟨τ,?_,?_,?_⟩
  · change (τ₀.modulus ⊓ (primaryCharacter r (supported_element_ne_zero r hr) χ).modulus) ⊓
      (primaryRayCharacter ξ).modulus=_
    rw [hM,primaryCharacter_modulus,primaryRayCharacter_modulus,inf_eq_left.mpr hp.1,inf_eq_left.mpr hp.2]
  · intro n
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_all]
  · intro n hn hpn
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_primary r _ χ n hpn,
      primaryRayCharacter_primary ξ n hn hpn,rowTwist_extract_sixth_mask _ m 1 (e*r) n ((supported_iff_native _).mp hn)]
    simp only [one_pow,one_mul]
    rfl

end CenteredMomentFirstFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstCanonicalFamily
open Eisenstein  
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstFamily
open CenteredMomentFirstColumns CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
local notation "O" => Eisenstein.O

theorem supported_of_dvd (A B : Ideal O) (hB : Supported B) (hd : A∣B) : Supported A := by
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ] at hB
  exact ((supported_mul_iff A Q).mp hB).1

theorem activeConductor_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {activeConductor I J}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (activeConductor_span_dvd I J)

theorem subsetGenerator_span_dvd (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}∣commonPart I J := by
  rw [TruncatedPrincipalPoisson.primeSubsetGenerator_span]
  refine (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem subsetGenerator_supported (I J : Ideal O) (hI : Supported I)
    (E : Finset (CommonIndex I J)) :
    Supported (Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (subsetGenerator_span_dvd I J E)

def canonicalActiveCharacter (I J : Ideal O) (hI : Supported I) :
    MulChar (Residue (activeConductor I J)) ℂ :=
  primitiveCharacter (activePrime I J) (activeCoprime I J) (activeGood I J hI) (activeExponent I J)

@[simp] theorem canonicalActiveCharacter_mk (I J : Ideal O) (hI : Supported I) (n : O) :
    canonicalActiveCharacter I J hI (Ideal.Quotient.mk _ n)=
      finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) n :=
  primitiveCharacter_mk _ _ _ _ n

theorem exists_canonical_first_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (I J : Ideal O) (hI : Supported I) (E : Finset (CommonIndex I J))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let r := activeConductor I J
    let ρ := finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ n : O,Supported (Ideal.span {n}) → lambda^2∣n-1 →
        elementCoeff τ₁ n=elementCoeff η n*coprimalityMask m n*leftCoefficient e r ρ n*rayMonoid ξ₁ n) ∧
      (∀ n : O,Supported (Ideal.span {n}) → lambda^2∣n-1 →
        elementCoeff τ₂ n=elementCoeff η n*coprimalityMask m n*rightCoefficient e r ρ n*rayMonoid ξ₂ n) := by
  dsimp only
  obtain ⟨τ₁,hM₁,_,h₁⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI) ξ₁
  obtain ⟨τ₂,hM₂,_,h₂⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI)⁻¹ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro n hn hp
    rw [h₁ n hn hp,canonicalActiveCharacter_mk,leftCoefficient]
    ring
  · intro n hn hp
    let : Finite (Residue (activeConductor I J)) := finiteEisensteinQuotientOfNonzero (finitePrimeModulus_ne_zero (activePrime I J))
    rw [h₂ n hn hp,← MulChar.star_apply',canonicalActiveCharacter_mk,rightCoefficient]
    ring

theorem first_displayed_norm (η : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) :
    (η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}).absNorm =
    η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏ P∈E,P.val).absNorm*(Ideal.span {activeConductor I J}).absNorm) := by
  rw [← Ideal.span_singleton_mul_span_singleton,TruncatedPrincipalPoisson.primeSubsetGenerator_span]
  simp only [map_mul]

end CenteredMomentFirstCanonicalFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstEnergy
open CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentHeckeExpansion HeckeFamily 
local notation "O" => Eisenstein.O

theorem finiteHeckeEnergy_reduced_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          reducedFirstSum I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sourceGenerator,sourceGenerator,
    primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2,
    canonical_pair_reduced_poisson]
  exact hK

end CenteredMomentFirstEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

theorem primeSupport_mul (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    primeSupport (I*J)=primeSupport I∪primeSupport J := by
  simp only [primeSupport,normalizedFactors_mul hI hJ,Multiset.toFinset_add]

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

theorem reconstructed_commonSupport (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonSupport (C*a) (D*b)=primeSupport C := by
  unfold commonSupport
  rw [primeSupport_mul C a hC ha,primeSupport_mul D b hD hb,← hCD]
  have h₁ := (CenteredMomentSupport.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (CenteredMomentSupport.primeSupport_disjoint_iff hC hb).mpr hCb
  have h₃ := (CenteredMomentSupport.primeSupport_disjoint_iff ha hb).mpr hab
  ext P
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hc|ha',hd|hb'⟩
    · exact hc
    · exact hc
    · exact hd
    · exact False.elim (Finset.disjoint_left.mp h₃ ha' hb')
  · exact fun hp => ⟨Or.inl hp,Or.inl hp⟩

theorem reconstructed_commonParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonPart (C*a) (D*b)=C ∧ commonPart (D*b) (C*a)=D := by
  have hs := reconstructed_commonSupport C D a b hC hD ha hb hCD hCa hCb hab
  have h₁ := (CenteredMomentSupport.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (CenteredMomentSupport.primeSupport_disjoint_iff hC hb).mpr hCb
  constructor
  · rw [commonPart_eq_supportExtract,hs,supportExtract_mul C a hC ha,
      supportExtract_of_subset C hC _ (Finset.Subset.refl _),supportExtract_of_disjoint a _ h₁.symm,mul_one]
  · rw [commonPart_eq_supportExtract,commonSupport_comm (D*b) (C*a),hs,
      supportExtract_mul D b hD hb,
      supportExtract_of_subset D hD _ (by rw [hCD]),supportExtract_of_disjoint b _ h₂.symm,mul_one]

theorem reconstructed_residualParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    residualPart (C*a) (D*b)=a ∧ residualPart (D*b) (C*a)=b := by
  obtain ⟨h₁,h₂⟩ := reconstructed_commonParts C D a b hC hD ha hb hCD hCa hCb hab
  constructor
  · apply mul_left_cancel₀ hC
    have he := reconstruct (C*a) (D*b) (mul_ne_zero hC ha)
    rw [h₁] at he
    exact he.symm
  · apply mul_left_cancel₀ hD
    have he := reconstruct (D*b) (C*a) (mul_ne_zero hD hb)
    rw [h₂] at he
    exact he.symm

end CenteredMomentCommonSectors

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstSectors
open CenteredMomentCompleteCommon CenteredMomentCommonSectors 
local notation "O" => Eisenstein.O

def residualPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  S.preimage (fun a => C*a) (by intro a ha b hb he;exact mul_left_cancel₀ hC he)

@[simp] theorem mem_residualPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) (a : Ideal O) :
    a∈residualPool C hC S ↔ C*a∈S := Finset.mem_preimage

def pairSector (C D : Ideal O) (S T : Finset (Ideal O)) : Finset (Ideal O × Ideal O) :=
  (S.product T).filter (fun p => commonPart p.1 p.2=C ∧ commonPart p.2 p.1=D)

def residualPairDomain (C D : Ideal O) (hC : C≠0) (hD : D≠0) (S T : Finset (Ideal O)) :
    Finset (Ideal O × Ideal O) :=
  ((residualPool C hC S).product (residualPool D hD T)).filter
    (fun p => IsCoprime C p.1 ∧ IsCoprime C p.2 ∧ IsCoprime p.1 p.2)

theorem residualPair_image (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) :
    (residualPairDomain C D hC hD S T).image (fun p => (C*p.1,D*p.2))=pairSector C D S T := by
  ext p
  rcases p with ⟨I,J⟩
  constructor
  · intro hp
    obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hp
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    obtain ⟨hpools,hCa,hCb,hab⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpools
    have has : C*a∈S := (mem_residualPool C hC S a).mp ha
    have hbs : D*b∈T := (mem_residualPool D hD T b).mp hb
    have ha0 : a≠0 := right_ne_zero_of_mul (hS _ has)
    have hb0 : b≠0 := right_ne_zero_of_mul (hT _ hbs)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨has,hbs⟩,
      reconstructed_commonParts C D a b hC hD ha0 hb0 hCD hCa hCb hab⟩
  · intro hp
    obtain ⟨hpools,hCI,hDJ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hIS,hJT⟩ := Finset.mem_product.mp hpools
    have hi : C*residualPart I J=I := by rw [← hCI];exact (reconstruct I J (hS I hIS)).symm
    have hj : D*residualPart J I=J := by rw [← hDJ];exact (reconstruct J I (hT J hJT)).symm
    refine Finset.mem_image.mpr ⟨(residualPart I J,residualPart J I),?_,Prod.ext hi hj⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,?_,residualParts_coprime I J⟩
    · exact (mem_residualPool C hC S _).mpr (by dsimp only;rw [hi];exact hIS)
    · exact (mem_residualPool D hD T _).mpr (by dsimp only;rw [hj];exact hJT)
    · rw [← hCI]
      exact commonPart_own_residual_coprime I J
    · rw [← hCI]
      exact commonPart_residualPart_coprime I J

theorem pairSector_sum (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) (F : Ideal O → Ideal O → ℂ) :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ p∈residualPairDomain C D hC hD S T,F (C*p.1) (D*p.2) := by
  rw [← residualPair_image C D hC hD hCD S T hS hT,Finset.sum_image]
  intro p hp q hq he
  exact Prod.ext (mul_left_cancel₀ hC (congrArg Prod.fst he))
    (mul_left_cancel₀ hD (congrArg Prod.snd he))

theorem pairSector_double_sum (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) (F : Ideal O → Ideal O → ℂ) :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ a∈residualPool C hC S,∑ b∈residualPool D hD T,
        if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F (C*a) (D*b) else 0 := by
  rw [pairSector_sum C D hC hD hCD S T hS hT,residualPairDomain,Finset.sum_filter]
  exact Finset.sum_product _ _ _

def commonLabels (S T : Finset (Ideal O)) : Finset (Ideal O × Ideal O) :=
  (S.product T).image (fun p => (commonPart p.1 p.2,commonPart p.2 p.1))

theorem commonLabels_data (S T : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels S T) :
    C≠0 ∧ D≠0 ∧ primeSupport C=primeSupport D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  exact ⟨commonPart_ne_zero _ _,commonPart_ne_zero _ _,commonParts_equal_support _ _⟩

theorem sum_common_sectors (S T : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ I∈S,∑ J∈T,F I J)=
      ∑ p∈commonLabels S T,∑ q∈pairSector p.1 p.2 S T,F q.1 q.2 := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s:=S.product T) (t:=commonLabels S T)
    (g:=fun p : Ideal O × Ideal O => (commonPart p.1 p.2,commonPart p.2 p.1))
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (fun p : Ideal O × Ideal O => F p.1 p.2)
  symm
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro p hp
    rcases p with ⟨C,D⟩
    congr 1
    ext q
    simp only [pairSector,Finset.mem_filter,Prod.mk.injEq]
  · exact (Finset.sum_product S T (fun p : Ideal O × Ideal O => F p.1 p.2)).symm

end CenteredMomentFirstSectors

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstSectorEnergy
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentCompleteCommon
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentActive CenteredMomentFourier 
local notation "O" => Eisenstein.O

def originalKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖ringComplex z‖^2/K)

theorem energy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
            originalKernel q.1 q.2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  have hspan (I : supportedColumns S) : Ideal.span {sourceGenerator S I} = I :=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp_rw [hspan]
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K)=_
  let F := fun I J : Ideal O =>
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem sector_independent_columns (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
              originalKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

def fixedFirstSum (C D : Ideal O) (hC : Supported C) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let k := K/‖ringComplex e‖^2
    let r := activeConductor C D
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) e*
      (((k/‖ringComplex (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter a ha)
          (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) h*
          paperRadialFourier W (k*‖ringComplex h‖^2/‖ringComplex (a*(b*r))‖^2))

theorem originalKernel_fixed_first (C D : Ideal O) (hC : Supported C) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    originalKernel (C*Ideal.span {a}) (D*Ideal.span {b}) W K=fixedFirstSum C D hC a b ha hb W K := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero b hb)
  obtain ⟨h₁,h₂⟩ := fixed_common_parts C D hC.1 hD hCD
  have he := common_residual_reduced_poisson (fun P : CommonIndex C D => P.val) Subtype.val_injective
    (common_good C D hC) (common_odd C D hC) Finset.univ (leftExponent C D) (rightExponent C D)
    (fun P _ => ne_of_gt (leftExponent_pos C D P)) (fun P _ => ne_of_gt (rightExponent_pos C D P))
    a b (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ W K hK
  change _=fixedFirstSum C D hC a b ha hb W K at he
  rw [← he]
  unfold originalKernel
  apply tsum_congr
  intro z
  rw [← MulChar.star_apply',supportedModulusCharacter_mk,supportedModulusCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product,h₁,h₂]
  simp only [map_mul,star_mul]
  ring

end CenteredMomentFirstSectorEnergy

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
