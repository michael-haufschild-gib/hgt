/-
Initial residual tuples adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialDetectorSources

/-!
# Initial residual tuples

Slot ratios of the common profile, pool lists and active indices of the overlap ideal Fourier
expansion; compact residual profiles separate into Fourier densities and prime marks; residual
tuple and uniform energies.
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


noncomputable section

open scoped BigOperators Classical
open Eisenstein _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve  UniqueFactorizationMonoid
namespace InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=> Eisenstein.O

theorem reconstruct_outside (E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)(hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (quadraticIdealQuotient_dvd hres))

theorem columns_filter (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P):
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem residual_filtered (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hout:outside E c
  · rw [if_pos hout]
  · rw [if_neg hout]
    simp only [overlapResidualCoefficient,hη c hout,mul_zero,zero_mul]

theorem residual_deleted_filtered (χ:Character)(A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j
      (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u :=
  residual_filtered A E hE hPs hj hP _ (deleted_zero_outside χ E hE) a W Z r z G u

end InverseInitialExcludedOverlap

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
namespace InverseInitialCommonLists
open InverseMoment
local notation "Eis"=> Eisenstein.O
variable {σ:Type*} [DecidableEq σ]

private theorem prime_dvd_prime_iff_eq {P Q : Ideal Eis}
    (hP : Prime P) (hQ : Prime Q) : P ∣ Q ↔ P = Q := by
  constructor
  · intro hd
    let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero
    by_contra hn
    exact hP.not_unit ((Ideal.isCoprime_of_isMaximal hn).isRelPrime (dvd_refl P) hd)
  · rintro rfl
    exact dvd_refl _

def poolList (F:Finset (Ideal Eis))(L:Finset (Ideal Eis)) : Finset (primePool F) :=
  Finset.univ.filter (fun i=> i.val∈L)

theorem outside_pool_not_dvd (F:Finset (Ideal Eis))(A:Finset (primePool F))
    {P:Ideal Eis}(hP:Prime P)(hn:P∉primePool F) : ¬P∣∏i∈A,i.val := by
  intro hd
  obtain ⟨i,hi,hd⟩ := hP.dvd_finsetProd_iff (fun i:primePool F=> i.val) |>.mp hd
  have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have he := (prime_dvd_prime_iff_eq hP hip).mp hd
  exact hn (he ▸ i.property)

theorem dividing_list_image (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(A:Finset (primePool F)) :
    ((poolList F L).filter (fun i=> i∈A)).image Subtype.val=
      L.filter (fun P=> P∣∏i∈A,i.val) := by
  ext P
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiL,hiA⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiL).2,Finset.dvd_prod_of_mem _ hiA⟩
  · intro h
    obtain ⟨hPL,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,hd⟩ := (hL P hPL).dvd_finsetProd_iff (fun i:primePool F=> i.val) |>.mp hd
    have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (hL P hPL) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hPL⟩

theorem original_ideal_slot (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(a:Ideal Eis→ℂ)(A:Finset (primePool F)) :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=> a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (fun i _ j _ h=> Subtype.val_injective h)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark (F:Finset (Ideal Eis))(I:Finset σ)
    (L:σ→ Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→ Ideal Eis→ℂ)(A:Finset (primePool F)) :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=> poolList F (L i)) (fun i q=> a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact original_ideal_slot F (L i) (hL i hi) (a i) A

end InverseInitialCommonLists

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation Eisenstein
namespace InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier
local notation "Eis"=> Eisenstein.O
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def activeIndices (primes : ι→ Ideal Eis) (I : Finset σ) (L : σ→ Finset ι)
    (c : Ideal Eis) : Finset ι := (I.biUnion L).filter (fun p=> primes p∣c)

omit [DecidableEq σ] in
theorem activeIndices_mem (primes : ι→ Ideal Eis) (I : Finset σ) (L : σ→ Finset ι)
    (c : Ideal Eis) {i : σ} (hi : i∈I) {p : ι} (hp : p∈L i) :
    p∈activeIndices primes I L c ↔ primes p∣c := by
  simp only [activeIndices,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,hi,hp⟩)

theorem indexed_mark_active (primes : ι→ Ideal Eis) (I : Finset σ) (L : σ→ Finset ι)
    (a : σ→ι→ℂ) (c : Ideal Eis) :
    indexedIdealMark primes I L a c=primeMark I L a (activeIndices primes I L c) := by
  unfold indexedIdealMark primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  simp only [activeIndices_mem primes I L c hi hp]

theorem indexed_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→ Ideal Eis) (I : Finset σ) (L : σ→ Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*kernelLogPhase t xc*
        indexedIdealMark primes I L (fun i p=> a i p*kernelLogPhase (-t) (y i p)) c := by
  simp_rw [indexed_mark_active]
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [activeIndices_mem primes I L c i.property ((Finset.mem_pi.mp hp) i.val i.property)]

theorem indexed_overlap_integrable (g : 𝓢(ℝ,ℂ))
    (primes : ι→ Ideal Eis) (I : Finset σ) (L : σ→ Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    Integrable (fun t:ℝ=> density g xj t*kernelLogPhase t xc*
      indexedIdealMark primes I L (fun i p=> a i p*kernelLogPhase (-t) (y i p)) c) := by
  simp_rw [indexed_mark_active]
  exact overlap_mode_integrable g I L a y _ xj xc

omit [DecidableEq σ] [DecidableEq ι] in
theorem tuple_gate_product (primes : ι→ Ideal Eis) (I : Finset σ)
    (a : σ→ι→ℂ) (p : ∀i∈I,ι) (c : Ideal Eis)
    (hc : Pairwise (Function.onFun IsCoprime (fun i:I=> primes (p i.val i.property)))) :
    (∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)=
      if (∏i∈I.attach,primes (p i.val i.property))∣c then
        ∏i∈I.attach,a i.val (p i.val i.property) else 0 := by
  by_cases h : (∏i∈I.attach,primes (p i.val i.property))∣c
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i hi
    exact if_pos ((Finset.dvd_prod_of_mem (fun i:I=> primes (p i.val i.property)) hi).trans h)
  · rw [if_neg h]
    have hn : ∃i:I,¬primes (p i.val i.property)∣c := by
      by_contra hn
      push_neg at hn
      apply h
      exact Finset.prod_dvd_of_coprime (hc.set_pairwise _) (fun i _=> hn i)
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_attach _ i) (if_neg hi)

theorem finite_ideal_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→ Ideal Eis) (I : Finset σ) (L : σ→ Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (C : Finset (Ideal Eis))
    (coefficient : Ideal Eis→ℂ) (xj : ℝ) (xc : Ideal Eis→ℝ) :
    (∑c∈C,coefficient c*
      ∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
        g (xj+xc c-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*
        ∑c∈C,coefficient c*kernelLogPhase t (xc c)*
          indexedIdealMark primes I L (fun i p=> a i p*kernelLogPhase (-t) (y i p)) c := by
  simp_rw [indexed_overlap_separation]
  simp only [Finset.mul_sum]
  have hi (c:Ideal Eis) : Integrable (fun t:ℝ=> coefficient c*
      (density g xj t*kernelLogPhase t (xc c)*indexedIdealMark primes I L
        (fun i p=> a i p*kernelLogPhase (-t) (y i p)) c)) :=
    (indexed_overlap_integrable g primes I L a y c xj (xc c)).const_mul _
  have he (c:Ideal Eis) (t:ℝ) : density g xj t*(coefficient c*kernelLogPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=> a i p*kernelLogPhase (-t) (y i p)) c)=
      coefficient c*(density g xj t*kernelLogPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=> a i p*kernelLogPhase (-t) (y i p)) c) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun c _=> hi c)]
  simp only [integral_const_mul]

end InverseInitialOverlapIdealFourier

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseInitialOverlapSource
open InverseInitialOverlapFresh InverseInitialOverlapInputFourier
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def tupleCoordinate (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) (i : σ) : ℝ :=
  if hi:i∈I then y i (q i hi) else 1

omit [DecidableEq ι] in
theorem tupleCoordinate_product (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) :
    (∏i∈I,tupleCoordinate I y q i)=∏i∈I.attach,y i.val (q i.val i.property) := by
  rw [←Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [tupleCoordinate,dif_pos i.property]

theorem insert_original_fresh
    (I : Finset σ) (L : σ→ Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (lo hi : σ→ℝ) (W wFresh : ℝ→ℂ) (a₀ b₀ jlo jhi : ℝ)
    (_hW : Function.support W⊆Set.Icc a₀ b₀)
    (ha : ∀i∈I,∀q∈L i,a i q≠0→ y i q∈Set.Icc (lo i) (hi i))
    (hFresh : ∀(v:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,v i∈Set.Icc (lo i) (hi i))→ yj∈Set.Icc jlo jhi→0< yc→
      W (yj*yc/(∏i∈I,v i))≠0→ wFresh yc=1)
    (A : Finset ι) (yj yc : ℝ) (hj : yj∈Set.Icc jlo jhi) (hc : 0< yc) :
    wFresh yc*(∑q∈I.pi L,
      (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
        W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))) =
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)=0
  · simp only [hz,zero_mul,mul_zero]
  by_cases hw : W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))=0
  · simp only [hw,mul_zero]
  have hcoord : ∀i∈I,tupleCoordinate I y q i∈Set.Icc (lo i) (hi i) := by
    intro i hi
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi⟩ (Finset.mem_attach _ _)
    have hcoeff : a i (q i hi)≠0 := by
      intro he
      apply hn
      split_ifs
      · exact he
      · rfl
    simpa only [tupleCoordinate,dif_pos hi] using
      ha i hi (q i hi) ((Finset.mem_pi.mp hq) i hi) hcoeff
  have hf := hFresh (tupleCoordinate I y q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  rw [hf,one_mul]


end InverseInitialOverlapSource
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation Eisenstein CompletedGauss 
namespace InverseInitialCommonProfile
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios
open InverseInitialOverlapFourier InverseInitialOverlapIdealFourier
local notation "Eis"=> Eisenstein.O
variable {σ:Type*} [DecidableEq σ]

def slotRatio (Z:ℝ)(ell:σ→ℝ)(i:σ)(P:Ideal Eis) : ℝ := (P.absNorm:ℝ)/Z^(ell i)

omit [DecidableEq σ] in
theorem slotRatio_pos (Z:ℝ)(hZ:0< Z)(ell:σ→ℝ)(i:σ){P:Ideal Eis}(hP:Prime P) :
    0< slotRatio Z ell i P := by
  apply div_pos _ (Real.rpow_pos_of_pos hZ _)
  exact_mod_cast Nat.pos_of_ne_zero (fun h=> hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))

theorem common_profile_separation
    (W:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0< a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→ Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→ Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime
      (fun i:I=> q i.val i.property)))
    (Z:ℝ)(hZ:0< Z)(ell:σ→ℝ)(A:Finset (primePool F))
    (yj yc:ℝ)(hj:0< yj)(hc:0< yc) :
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if survivingProduct I q∣(∏i∈A,i.val) then
        W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)) =
      ∫t:ℝ,density (kernelLogSource W a₀ b₀ ha₀ hs hW)
        (Real.log yj) t*kernelLogPhase t (Real.log yc)*
        primeMark I (fun i=> poolList F (L i))
          (fun i q=> a i q.val*kernelLogPhase (-t) (Real.log (slotRatio Z ell i q.val))) A := by
  have hm (t:ℝ) : primeMark I (fun i=> poolList F (L i))
      (fun i q=> a i q.val*kernelLogPhase (-t) (Real.log (slotRatio Z ell i q.val))) A =
      primeMark I L (fun i P=> a i P*kernelLogPhase (-t) (Real.log (slotRatio Z ell i P)))
        (activeIndices id I L (∏i∈A,i.val)) :=
    (original_ideal_mark F I L hL
      (fun i P=> a i P*kernelLogPhase (-t) (Real.log (slotRatio Z ell i P))) A).symm.trans
      (indexed_mark_active id I L _ _)
  simp_rw [hm]
  have he := actual_overlap_separation W a₀ b₀ ha₀ hs hW I L a (slotRatio Z ell)
    (fun i hi P hP=> slotRatio_pos Z hZ ell i (hL i hi P hP))
    (activeIndices id I L (∏i∈A,i.val)) yj yc hj hc
  have hprofile : CanonicalCubeSeparation.sourceLogProfile W a₀ b₀ ha₀ hs hW =
      kernelLogSource W a₀ b₀ ha₀ hs hW := by
    ext x
    rw [CanonicalCubeSeparation.sourceLogProfile_apply,kernelLogSource_apply]
  rw [hprofile] at he
  rw [←he]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L (∏i∈A,i.val)
      then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣(∏i∈A,i.val) then
        ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣(∏i∈A,i.val) then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q (∏i∈A,i.val) (hcop q hq) using 1
  rw [hprod]
  split_ifs <;> simp

theorem common_profile_integrable (g:𝓢(ℝ,ℂ))
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→ Finset (Ideal Eis))
    (a:σ→ Ideal Eis→ℂ)(Z:ℝ)(ell:σ→ℝ)(A:Finset (primePool F))(yj yc:ℝ) :
    Integrable (fun t:ℝ=> density g (Real.log yj) t*kernelLogPhase t (Real.log yc)*
      primeMark I (fun i=> poolList F (L i))
        (fun i q=> a i q.val*kernelLogPhase (-t) (Real.log (slotRatio Z ell i q.val))) A) :=
  overlap_mode_integrable g I (fun i=> poolList F (L i)) (fun i q=> a i q.val)
    (fun i q=> Real.log (slotRatio Z ell i q.val)) A (Real.log yj) (Real.log yc)

end InverseInitialCommonProfile

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap
open Eisenstein
namespace InverseInitialCommonCutoff
open InverseMoment InverseInitialCommonProfile InverseInitialCommonRatios
open InverseInitialOverlapIdealFourier InverseInitialOverlapSource
local notation "Eis"=> Eisenstein.O
variable {σ:Type*} [DecidableEq σ]

def tupleProfile (I:Finset σ)(L:σ→ Finset (Ideal Eis))(a:σ→ Ideal Eis→ℂ)
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) : ℂ :=
  ∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
    (if survivingProduct I q∣c then
      W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)

theorem tupleProfile_gates (I:Finset σ)(L:σ→ Finset (Ideal Eis))(a:σ→ Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=> q i.val i.property)))
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) :
    tupleProfile I L a Z ell W yj yc c=
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) := by
  apply Finset.sum_congr rfl
  intro q hq
  have hg : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣c then ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣c then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q c (hcop q hq) using 1
  rw [hg]
  split_ifs <;> simp

theorem tupleProfile_insert_fresh
    (I:Finset σ)(L:σ→ Finset (Ideal Eis))(a:σ→ Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=> q i.val i.property)))
    (Z:ℝ)(ell lo hi:σ→ℝ)(W wFresh:ℝ→ℂ)(a₀ b₀ jlo jhi:ℝ)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (ha:∀i∈I,∀q∈L i,a i q≠0→ slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0< yc→ W (yj*yc/(∏i∈I,v i))≠0→ wFresh yc=1)
    (yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hc:0< yc)(c:Ideal Eis) :
    wFresh yc*tupleProfile I L a Z ell W yj yc c=tupleProfile I L a Z ell W yj yc c := by
  rw [tupleProfile_gates I L a hcop]
  exact insert_original_fresh I L a (slotRatio Z ell) lo hi W wFresh a₀ b₀ jlo jhi
    hs ha hFresh (activeIndices id I L c) yj yc hj hc

end InverseInitialCommonCutoff

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
open  SecondPassArithmetic FirstPassCubeLabels
namespace InverseInitialCommonTransform
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=> Eisenstein.O
variable {σ:Type*} [DecidableEq σ]

/-- A compact residual profile separates into its Fourier density and finite prime marks. -/
theorem original_profile_point
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0< a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→ Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→ Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=> q i.val i.property)))
    (Z:ℝ)(hZ:0< Z)(ell lo hi:σ→ℝ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→ slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0< yc→ W (yj*yc/(∏i∈I,v i))≠0→ wFresh yc=1)
    (A:Finset (primePool F))(yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hjpos:0< yj)(hc:0< yc) :
    tupleProfile I L a Z ell W yj yc (∏i∈A,i.val)=
      ∫t:ℝ,density (kernelLogSource W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (primeMark I (fun i=> poolList F (L i))
          (fun i q=> a i q.val*kernelLogPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
          childLogTest wFresh t yc) := by
  have he := common_profile_separation W a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell A yj yc hjpos hc
  have hcut := tupleProfile_insert_fresh I L a hcop Z ell lo hi W wFresh a₀ b₀ jlo jhi hs ha hFresh yj yc hj hc (∏i∈A,i.val)
  rw [←hcut]
  unfold tupleProfile
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold childLogTest
  ring


end InverseInitialCommonTransform
end

end

noncomputable section
open TruncatedPrincipalPoisson Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open InverseInitialOverlap InverseInitialRayAttachment
open InverseMoment
namespace InverseInitialEnergyCallerSelector
local notation "Eis" => Eisenstein.O

theorem mask_nonzero_coprime (F : Finset (Ideal Eis)) (j : Ideal Eis) (hj : CanonicalQuadraticSieve.Admissible j)
    (A : Finset (primePool F))
    (hm : rowCoprimeMask (fun i : primePool F=> i.val) A (primaryIdealGenerator j)≠0) :
    IsCoprime (∏ i∈A,i.val) j := by
  have hspan := CenteredMomentSourceRow.primary_span_supported j (admissible_supported hj)
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : i.val.IsMaximal) htop
    (show (i.val : Ideal Eis) ≤ (i.val : Ideal Eis) ⊔ j from le_sup_left)
  have hmem : primaryIdealGenerator j∈i.val := by
    rw [he]
    apply (show j ≤ (i.val : Ideal Eis) ⊔ j from le_sup_right)
    have hjmem : primaryIdealGenerator j ∈ Ideal.span {primaryIdealGenerator j} :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hspan] at hjmem
    exact hjmem
  apply hm
  rw [CenteredMomentActive.rowCoprimeMask_ideal_indicator]
  exact if_pos ⟨i,hi,hmem⟩


end InverseInitialEnergyCallerSelector
end

end

noncomputable section
open TruncatedPrincipalPoisson Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open SecondPassArithmetic
namespace InverseInitialCommonForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic 
open InverseInitialEnergyCallerWindow InverseInitialEnergyCallerSelector
local notation "Eis"=> Eisenstein.O

theorem common_selector_window
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0< Z)(hW:∀x,W x≠0→ x≤ b)
    {P j:Ideal Eis}(hP:CanonicalQuadraticSieve.Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,CanonicalQuadraticSieve.Admissible I)(A:Finset (primePool F)) :
    (if (∏i∈A,i.val)∈columns (originalSource Z r b) P j then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=> i.val) A (primaryIdealGenerator j) =
    (if residual P j∣(∏i∈A,i.val) then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=> i.val) A (primaryIdealGenerator j) := by
  by_cases hm : rowCoprimeMask (fun i:primePool F=> i.val) A (primaryIdealGenerator j)=0
  · simp only [hm,mul_zero]
  by_cases hw : residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))=0
  · simp only [hw,ite_self,zero_mul]
  have hA := ((admissible_iff_native _).mpr (CanonicalRowCompletion.poolProduct_admissible F (fun I hI => (admissible_iff_native I).mp (hF I hI)) A))
  have hcop := mask_nonzero_coprime F j (InverseMoment.descentAdmissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA.2.1,hcop,hd,
      reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hd hw⟩
    simp only [hd,hmem,ite_true]
  · have hn : (∏i∈A,i.val)∉columns (originalSource Z r b) P j :=
      fun h=> hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [hd,hn,ite_false]


end InverseInitialCommonForcing
end

end

noncomputable section
open TruncatedPrincipalPoisson Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open SecondPassArithmetic UniqueFactorizationMonoid CanonicalRowCompletion
namespace InverseInitialLargePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic 
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialCommonTuples
local notation "Eis"=> Eisenstein.O
local notation "O"=> Eisenstein.O
theorem selected_conjugate_row_supported (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,CanonicalQuadraticSieve.Admissible I) (j : Ideal O) (hj : CanonicalQuadraticSieve.Admissible j)
    (η : Ideal O →* ℂ) (H : Ideal O → ℂ) (hcop : ∀ I ∈ F,H I≠0 → IsCoprime I j) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) Finset.univ
        (elementCharacter η) (primaryIdealGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)))
  dsimp only
  rw [CanonicalRowCompletion.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  erw [initial_input_row]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    by_cases hh : H (∏i∈A,i.val)=0
    · simp only [hh,mul_zero,zero_mul]
    rw [selected_mask F (poolPrimary F) (poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI))) j hj A (hcop _ hAF hh),mul_one]
    have hr := idealRowHom_product (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI))) A u
    rw [span_finset_prime_product] at hr
    simp only [he] at hr
    rw [hr]
    rw [prime_product_moebius (fun i : primePool F => i.val)
      (fun i => Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance) Subtype.val_injective A]
    simp only [supportMobius]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_large_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : CanonicalQuadraticSieve.Admissible P) (hj : j∣P) (hF : ∀I∈F,CanonicalQuadraticSieve.Admissible I)
    (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) Finset.univ
        (elementCharacter η) (primaryIdealGenerator j) 1 1
        (fun A=> if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
  let H : Ideal Eis→ℂ := fun c=> if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=> c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=> hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  have hcH : ∀I∈F,H I≠0→ IsCoprime I j := by
    intro I hIF hHI
    by_cases hi:I∈columns S P j
    · exact ((mem_columns hP.2.1 hj).mp hi).2.1
    · exact False.elim (hHI (by simp [H,hi]))
  rw [he,selected_conjugate_row_supported F hF j (InverseMoment.descentAdmissible_of_dvd hP hj) η H hcH u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]


end InverseInitialLargePool
end

end

noncomputable section
open TruncatedPrincipalPoisson Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open SecondPassArithmetic UniqueFactorizationMonoid
namespace InverseInitialExcludedForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic 
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedOverlap
open InverseInitialCommonTuples InverseInitialCommonTransform
local notation "O"=> Eisenstein.O

theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=> i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))

/-- Removing excluded primes leaves exactly the residual divisibility gate in the input row. -/
theorem residual_excluded_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0< Z)(hW:∀x,W x≠0→ x≤ b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    {P j:Ideal O}(hP:CanonicalQuadraticSieve.Admissible P)(hj:j∣P)(hPE:outside E P)
    (F:Finset (Ideal O))(hF:∀I∈F,CanonicalQuadraticSieve.Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:columns (originalOutside (originalSource Z r b) E) P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(u:O):
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) Finset.univ
        (elementCharacter η) (primaryIdealGenerator j) 1 1
        (fun A=> if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
  rw [residual_filtered _ E hE hP.2.1 hj hPE η hη,
    residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI))),
    initial_input_row (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)))]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:=common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm:primeCoprimeMask (poolPrimary F) A
      (primaryIdealGenerator j)=rowCoprimeMask (fun i:primePool F=> i.val) A (primaryIdealGenerator j):=by
    rw [TruncatedPrincipalPoisson.rowCoprimeMask]
    simp only [primeCoprimeMask_indicator, ←Ideal.mem_span_singleton,
      poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)), span_cubicIdealGenerator]
  have hmem:((∏i∈A,i.val)∈columns (originalOutside (originalSource Z r b) E) P j)↔
      ((∏i∈A,i.val)∈columns (originalSource Z r b) P j):=by
    rw [columns_filter _ E hE hP.2.1 hj hPE,Finset.mem_filter]
    exact and_iff_left (pool_product_outside F E hE hFE A)
  dsimp only
  simp only [hm,hmem]
  linear_combination
    (supportMobius A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (primeSubsetRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) A u))*he

variable {κ:Type*}
theorem original_tuples_excluded_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0< Z)(hW:∀x,W x≠0→ x≤ b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (T:Finset κ)(P:κ→ Ideal O)(j:Ideal O)
    (hP:∀k∈T,CanonicalQuadraticSieve.Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (F:Finset (Ideal O))(hF:∀I∈F,CanonicalQuadraticSieve.Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:tupleColumns (originalOutside (originalSource Z r b) E) T P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(a:κ→ℂ)(u:O) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) Finset.univ
        (elementCharacter η) (primaryIdealGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_excluded_forcing W Z r z G b hZ hW E hE (hP k hk) (hj k hk) (hPE k hk) F hF hFE
    (fun c hc=> hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η hη u]
  ring

end InverseInitialExcludedForcing

end

end

noncomputable section
open TruncatedPrincipalPoisson Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
open  SecondPassArithmetic FirstPassCubeLabels
namespace InverseInitialExcludedFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=> Eisenstein.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedForcing
theorem original_tuples_excluded_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0< a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal Eis))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→ Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→ Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,CanonicalQuadraticSieve.Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=> q i.val i.property)))
    (hPE:∀q∈I.pi L,outside E (j*survivingProduct I q))
    (η:Ideal Eis→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:Eis)(Z r z G:ℝ)(hZ:0< Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→ slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0< yc→ W (yj*yc/(∏i∈I,v i))≠0→ wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,CanonicalQuadraticSieve.Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=> j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=> j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (kernelLogSource W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) Finset.univ
          (elementCharacter η) (primaryIdealGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=> poolList F (L i))
              (fun i q=> a i q.val*kernelLogPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=> by rw [poolPrimary_span F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=> hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := kernelLogSource W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=> density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=> poolList F (L i))
      (fun i q=> a i q.val*kernelLogPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(((admissible_iff_native _).mpr (CanonicalRowCompletion.poolProduct_admissible F (fun I hI => (admissible_iff_native I).mp (hF I hI)) A))).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_excluded_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2) E hE
    (I.pi L) P j hP (fun q _=> dvd_mul_right j _) hPE F hF hFE hsub η hη (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (fun i => complexSexticChar (Ideal.span {poolPrimary F i}) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)) i)) Finset.univ
    (elementCharacter η) (primaryIdealGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI))) Finset.univ
    (elementCharacter η) (primaryIdealGenerator j) u H (fun A _=> hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI))),
    initial_input_row (poolPrimary F) (poolPrimary_good F (fun I hI => (admissible_iff_native I).mp (hF I hI)))]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,CanonicalRowCompletion.poolPrimary_norm F (fun I hI => (admissible_iff_native I).mp (hF I hI))]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end InverseInitialExcludedFourier

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace InverseInitialResidualPool
open Eisenstein _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "O"=> Eisenstein.O

/-- A finite pool contains every residual column and the required norm range. -/
theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0< Z)(hBtree:0≤ Btree)
    (T:Finset κ)(P:κ→ Ideal O)(j:Ideal O)
    (hP:∀k∈T,CanonicalQuadraticSieve.Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤ Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (Real.rpow_nonneg hZ.le _)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (Real.rpow_nonneg hZ.le _) le_rfl,hcover⟩

end InverseInitialResidualPool

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace InverseInitialResidualTupleEnergy
open Eisenstein CompletedGauss  
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=> Eisenstein.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory JointLogSeparation JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
/-- The excluded Fourier expansion transfers the input energy estimate to original residual tuples. -/
theorem original_residual_tuple_energy
    (Woriginal W:ℝ→ℂ)(ao bo:ℝ)(hao:0< ao)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)(a₀ b₀ bcap:ℝ)(ha₀:0< a₀)(hbcap:1≤ bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤ B₀)(hb:∀x,‖W x‖≤ B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0< gap)(heps:0< eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤ gap/50)(hτ:0<τ)(hτsmall:τ≤ gap/50)(hloss:0< loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤ Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀Z:ℝ,Z₀≤ Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤ Dpool→
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    let _p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let _hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→ all.card≤ K→
    ∀(L:σ→ Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→ Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤ Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤ Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→ O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤ z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤ m→ m≤ cap→-cap≤ D→
      (∏i∈assigned,bl i)≤ Z^η→
      (∏i∈all\assigned,Hslot i)≤ Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖ringComplex u‖^2≤ Z^m)→
    ∀(j:Ideal O),CanonicalQuadraticSieve.Admissible j→ Ideal.span {assignedElement assigned qelem}=j→
    ∀(lo hi:σ→ℝ)(jlo jhi:ℝ),
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc jlo jhi→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→ slotRatio Z z i P∈Set.Icc (lo i) (hi i))→
      (∀v:σ→ℝ,∀yj yc:ℝ,(∀i∈all\assigned,v i∈Set.Icc (lo i) (hi i))→
        yj∈Set.Icc jlo jhi→0< yc→ Woriginal (yj*yc/(∏i∈all\assigned,v i))≠0→ W yc=1)→
      (∀t∈(all\assigned).pi L,CanonicalQuadraticSieve.Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=> t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
      tupleColumns (originalOutside (originalSource Z r bo) (reflectionExcludedPrimes q))
        ((all\assigned).pi L) (fun t=> j*survivingProduct (all\assigned) t) j⊆F→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalFourier.original_fourier_energy_bound
    (kernelLogSource Woriginal ao bo hao hso hWo)
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan lo hi jlo jhi hjratio hL hcoeff hFresh hP hcopTuple hPE hsub θ
  have hZp:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hdisPool:(all:Set σ).PairwiseDisjoint (fun i=> poolList F (L i)):=by
    intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro P hPi hPk
    exact (Finset.disjoint_left.mp (hdis hi hk hik))
      (Finset.mem_filter.mp hPi).2 (Finset.mem_filter.mp hPk).2
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK
    (fun i=> poolList F (L i)) Hslot (fun i P=> coeff i P.val) hdisPool hHs
    (fun i hi P hP=> hPs i hi P.val (Finset.mem_filter.mp hP).2)
    (fun i hi P hP=> hac i hi P.val (Finset.mem_filter.mp hP).2)
    qelem z al bl primeW hz hqe hprimeW hprimeLive (elementCharacter χ) hχ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    (fun i P=> Real.log (slotRatio Z z i P.val)) (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) θ
  have hsum:∑i∈all\assigned,z i=assignedCenter all z-assignedCenter assigned z:=by
    have hh:=Finset.sum_sdiff (f:=z) hassigned
    dsimp [assignedCenter]
    linarith
  have hgj:Ideal.span {primaryIdealGenerator j}=Ideal.span {assignedElement assigned qelem}:=
    (CenteredMomentSourceRow.primary_span_supported j (admissible_supported hj)).trans hspan.symm
  have hid (u:O):
      (∑t∈(all\assigned).pi L,(∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u)=
      ∫t:ℝ,density (frequencyTwist (kernelLogSource Woriginal ao bo hao hso hWo) θ)
        (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ (elementCharacter χ)
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) (fun i=> poolList F (L i))
            (fun i P=> coeff i P.val*kernelLogPhase (-t) (Real.log (slotRatio Z z i P.val))))
            (childLogTest W t) Z D) u):=by
    have hh:=InverseInitialExcludedFourier.original_tuples_excluded_fourier
      (childLogTest Woriginal θ) W ao bo hao
      ((InverseInitialOriginalHeight.child_support Woriginal θ).trans hso)
      (InverseInitialOriginalHeight.child_smooth Woriginal ao bo hao hso hWo θ)
      (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (all\assigned) L hL coeff j hj.1 hP hcopTuple hPE χ hout u Z r
      (assignedCenter all z) (assignedCenter assigned z) hZp z lo hi hsum jlo jhi hjratio hcoeff
      (fun v yj yc hv hyj hyc hn=> hFresh v yj yc hv hyj hyc
        (InverseInitialOriginalHeight.child_support Woriginal θ hn))
      F (fun I hI => (admissible_iff_native I).mpr (hFa I hI)) (fun I hI=>(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.2) hsub
    rw [hh,InverseInitialOriginalHeight.kernelLogSource_child]
    simp only [←hDeq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [InverseInitialInputReindex.input_puncture_span p hg Finset.univ (elementCharacter χ)
      (primaryIdealGenerator j) (assignedElement assigned qelem) hgj]
  simpa only [hid] using he

end InverseInitialResidualTupleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace InverseInitialResidualUniformEnergy
open Eisenstein CompletedGauss  
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=> Eisenstein.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory JointLogSeparation JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
/-- A common compact window gives a uniform residual energy bound for all slot assignments. -/
theorem original_residual_uniform_energy
    (Woriginal:ℝ→ℂ)(ao bo:ℝ)(hao:0< ao)(hab:ao≤ bo)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0< gap)(heps:0< eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤ gap/50)(hτ:0<τ)(hτsmall:τ≤ gap/50)(hloss:0< loss)(K:ℕ):
    ∃degree:ℕ,
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀Z:ℝ,Z₀≤ Z→
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→ all.card≤ K→
    ∀(L:σ→ Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→ Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤ Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤ Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→ O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤ z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤ m→ m≤ cap→-cap≤ D→
      (∏i∈assigned,bl i)≤ Z^η→
      (∏i∈all\assigned,Hslot i)≤ Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖ringComplex u‖^2≤ Z^m)→
    ∀(j:Ideal O),CanonicalQuadraticSieve.Admissible j→ Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→ slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈(all\assigned).pi L,CanonicalQuadraticSieve.Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=> t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨W,A,B,Bnorm,hA,hAB,hBn,hWc,hWs,hWb,hFresh⟩:=
    InverseInitialUniformFresh.exists_uniform_fresh K ao bo hao hab
  have hs:Function.support (W:ℝ→ℂ)⊆Set.Icc A B:=(subset_tsupport (W:ℝ→ℂ)).trans hWs
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialResidualTupleEnergy.original_residual_tuple_energy
    Woriginal W ao bo hao hso hWo A B 1 hA le_rfl hs (W.smooth ⊤) Φ hΦ hone Bnorm hBn hWb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan hjratio hL hcoeff hP hcopTuple hPE θ
  have hZp:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  obtain ⟨Dpool,hfloor,hcover⟩:=InverseInitialResidualPool.exists_original_complete_pool
    q Z r bo cap Btree hZp (zero_le_one.trans hBtree) ((all\assigned).pi L)
    (fun t=> j*survivingProduct (all\assigned) t) j hP (fun t _=> dvd_mul_right j _) hPE
  exact henergy Z hZ Dpool hfloor all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan (fun _=>1) (fun _=>2) 1 ((2:ℝ)^K) hjratio hL hcoeff
    (hFresh (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK) Woriginal hso)
    hP hcopTuple hPE hcover θ

end InverseInitialResidualUniformEnergy

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
