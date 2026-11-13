/-
Free reflection pools adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.PowerfulPartsAndReflectedBranches

/-!
# Free reflection pools

The signed divisor expansion is a product of local reflected brackets; unit and ramified powers
contribute norm-one phases. Free reflection pools, raw dual kernels and summability of the
normalized cusp kernels.
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

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap ContDiff

theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 : 1<n := lt_of_le_of_ne hn (Ne.symm h)
  have hl : 0<Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hl
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←he,pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 hp.le
    _ = _ := Nat.mul_comm _ _

def completedRowDyad (rows : Finset (Ideal O)) (j : ℕ) : Finset (Ideal O) :=
  rows.filter (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

def completedRowDyadicLength (K : ℝ) : ℕ := Nat.clog 2 ⌊K⌋₊

theorem completedRowDyad_bounds (rows : Finset (Ideal O)) (j : ℕ)
    (hrows : ∀I∈rows,I≠0) (I : Ideal O) (hI : I∈completedRowDyad rows j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hIr,hj⟩ := Finset.mem_filter.mp hI
  have hn : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (fun hz => hrows I hIr (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl := two_pow_clog_le_double (Ideal.absNorm I) hn
  rw [hj] at hu hl
  refine ⟨hrows I hIr,?_,?_⟩
  · have hh : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ) := by exact_mod_cast hl
    linarith
  · exact_mod_cast hu

theorem completedRowDyad_sum {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal O)) (K : ℝ) (hK : 0≤K)
    (hrows : ∀I∈rows,(Ideal.absNorm I:ℝ)≤K) (f : Ideal O→M) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),∑I∈completedRowDyad rows j,f I)=∑I∈rows,f I := by
  have hm : ∀I∈rows,Nat.clog 2 (Ideal.absNorm I)∈Finset.range (completedRowDyadicLength K+1) := by
    intro I hI
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 ((Nat.le_floor_iff hK).mpr (hrows I hI)))
  simpa only [completedRowDyad] using Finset.sum_fiberwise_of_maps_to hm f

theorem completedRowDyadic_top (K : ℝ) (hK : 1≤K) :
    (2:ℝ)^(completedRowDyadicLength K)≤2*K := by
  have hh := two_pow_clog_le_double ⌊K⌋₊ ((Nat.one_le_floor_iff K).mpr hK)
  have hr : (2:ℝ)^(completedRowDyadicLength K)≤2*(⌊K⌋₊:ℝ) := by exact_mod_cast hh
  exact hr.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0≤K)) (by norm_num))

theorem completedRowDyadic_scale (K : ℝ) (hK : 1≤K) (j : ℕ)
    (hj : j∈Finset.range (completedRowDyadicLength K+1)) : (2:ℝ)^j≤2*K :=
  (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans
    (completedRowDyadic_top K hK)

theorem completedRowDyadic_mass (K : ℝ) (hK : 1≤K) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)≤4*K ∧
    (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)≤16*K^2 := by
  have ht := completedRowDyadic_top K hK
  constructor
  · rw [geom_sum_eq (by norm_num : (2:ℝ)≠1),pow_succ]
    norm_num
    linarith
  · have he (j : ℕ) : ((2:ℝ)^j)^2=(4:ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 2,pow_mul]; norm_num
    simp_rw [he]
    rw [geom_sum_eq (by norm_num : (4:ℝ)≠1),pow_succ,←he]
    norm_num
    have hp := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^(completedRowDyadicLength K)) ht 2
    nlinarith

theorem completedRowDyadic_shape (s K X Q : ℝ) (hs : 0 ≤ s) (hK : 1≤K)
    (hX : 0<X) (hQ : 0<Q) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*Q)^s*((2:ℝ)^j+((2:ℝ)^j)^2*Q/X))≤
      (16*(2:ℝ)^s)*(K*Q)^s*(K+K^2*Q/X) := by
  have hb (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      ((2:ℝ)^j*Q)^s≤(2*(K*Q))^s := by
    apply Real.rpow_le_rpow (by positivity) _ hs
    have h := mul_le_mul_of_nonneg_right (completedRowDyadic_scale K hK j hj) hQ.le
    nlinarith
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      (2*(K*Q))^s*((2:ℝ)^j+((2:ℝ)^j)^2*Q/X) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hb j hj) (by positivity))
    _ = (2*(K*Q))^s*((∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)+
      (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)*Q/X) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_mul]
    _ ≤ (2*(K*Q))^s*(4*K+16*K^2*Q/X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (completedRowDyadic_mass K hK).1
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (completedRowDyadic_mass K hK).2 hQ.le) hX.le)
    _ ≤ (2*(K*Q))^s*(16*(K+K^2*Q/X)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ = 4*K+16*(K^2*Q/X) := by ring
        _ ≤ 16*(K+K^2*Q/X) := by linarith
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CompletedDyadic
open scoped BigOperators Classical

def completedRamifiedInitial : ℝ := (3:ℝ)^(-(4/3:ℝ))
def completedRamifiedStep : ℝ := (3:ℝ)^(1/3:ℝ)

theorem completedRamifiedInitial_pos : 0<completedRamifiedInitial := by
  unfold completedRamifiedInitial
  positivity

theorem completedRamifiedStep_gt_one : 1<completedRamifiedStep := by
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

theorem actual_ramified_scale (m : ℕ) :
    ramifiedScale completedRamifiedInitial completedRamifiedStep m=(3:ℝ)^(((m:ℝ)-4)/3) := by
  unfold ramifiedScale completedRamifiedInitial completedRamifiedStep
  rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
  congr 1
  ring

theorem actual_ramified_norm (m : ℕ) :
    (ramifiedScale completedRamifiedInitial completedRamifiedStep m)^3=(3:ℝ)^((m:ℝ)-4) := by
  rw [actual_ramified_scale,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem cusp_coefficient_normalization (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    (3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)=
      1/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  have hroot : Real.sqrt ((3:ℝ)^m)=(3:ℝ)^(m/6)*(3:ℝ)^(m/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hbroot : Real.sqrt (b^3)=b*Real.sqrt b := by
    rw [show b^3=b^2*b by ring,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) hn.le),Real.sqrt_mul (by positivity),hroot,hbroot]
  have hr1 : (3:ℝ)^(m/6)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr2 : (3:ℝ)^(m/3)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hbn : Real.sqrt b≠0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  field_simp


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

lemma completedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,lambda^2∣n-1→Ψ n=Φ n) (W : ℝ→ℂ) (X : ℝ) :
    completedT Ψ W X=completedT Φ W X := by
  unfold completedT
  apply tsum_congr
  intro p
  rw [completedMellinCoefficient,completedMellinCoefficient,
    h _ (primaryIdealGenerator_spec p.1.val p.1.property.2).2,
    h _ (primaryIdealGenerator_spec p.2.val p.2.property).2]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

theorem nonresidual_count_eq_on_fiber (I J Q P : Ideal O)
    (hI : I≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    (normalizedFactors I).count P=(normalizedFactors J).count P := by
  have ha := congrArg (fun A : Ideal O=>(normalizedFactors A).count P) hA
  simp only [normalizedFactors_rowPowerfulPart,Multiset.count_filter] at ha
  have ht := congrArg (fun A : Ideal O=>(normalizedFactors A).count P) hT
  simp only [rowMaskPart,normalizedFactors_squarefreeMaskPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at ht
  have hr0 : (normalizedFactors (rowResidualPart I Q)).count P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp hm).2
  simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at hr0
  by_cases hpq : P∣Q
  · simp only [hpq,ite_true] at ht
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha ht <;> omega
  · have hpi : P∣I := (hP.dvd_mul.mp hpool).resolve_right hpq
    have hci : 0<(normalizedFactors I).count P :=
      Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hpi⟩)
    simp only [hpq,not_false_eq_true,ite_true] at hr0
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha hr0 <;> omega

theorem nonresidual_prime_transport (I J F Q P : Ideal O)
    (hI : I≠0) (hJ : J≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    P∣J*Q ∧ ¬P∣rowResidualPart J Q ∧ completedLocalExponent I F P=completedLocalExponent J F P := by
  have hc := nonresidual_count_eq_on_fiber I J Q P hI hP hA hT hpool hr
  have hpoolJ : P∣J*Q := by
    rcases hP.dvd_mul.mp hpool with hi|hq
    · have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hi⟩
      have hcj : 0<(normalizedFactors J).count P := hc ▸ Multiset.count_pos.mpr hm
      exact dvd_mul_of_dvd_left ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hJ).mp (Multiset.count_pos.mp hcj)).2 Q
    · exact dvd_mul_of_dvd_right hq J
  have hrc : (normalizedFactors (rowResidualPart I Q)).count P=
      (normalizedFactors (rowResidualPart J Q)).count P := by
    simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
      normalizedFactors_rowSimplePart,Multiset.count_filter,hc]
  refine ⟨hpoolJ,?_,?_⟩
  · intro hd
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart J) Q)).mpr ⟨hP,hd⟩
    have hp : 0<(normalizedFactors (rowResidualPart I Q)).count P := hrc.symm ▸ Multiset.count_pos.mpr hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
      (Multiset.count_pos.mp hp)).2
  · simp only [completedLocalExponent,hc]

lemma completedResidualScale_eq_on_fiber (K : ℝ) (I J Q : Ideal O)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q) :
    completedResidualScale K I Q=completedResidualScale K J Q := by
  simp only [completedResidualScale,hA,hT]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

def completedReflectionPool (I Q:Ideal O) : Finset (Ideal O) :=
  (primeSupport (I*Q)).filter (fun P=>lambda∉P ∧ ringChar (O⧸P)≠2 ∧ ¬P∣rowResidualPart I Q)

lemma mem_completedReflectionPool (I Q P:Ideal O) (hI:I≠0) (hQ:Q≠0) :
    P∈completedReflectionPool I Q ↔
      Prime P ∧ P∣I*Q ∧ lambda∉P ∧ ringChar (O⧸P)≠2 ∧ ¬P∣rowResidualPart I Q := by
  simp only [completedReflectionPool,Finset.mem_filter,primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)]
  aesop

lemma completedReflectionPool_maximal (I Q:Ideal O) (P:completedReflectionPool I Q) :
    P.val.IsMaximal := by
  have hm: P.val∈normalizedFactors (I*Q):=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp P.property).1
  have hp:=prime_of_normalized_factor P.val hm
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

lemma completedReflectionPool_good (I Q:Ideal O) (P:completedReflectionPool I Q) :
    lambda∉P.val := (Finset.mem_filter.mp P.property).2.1

lemma completedReflectionPool_odd (I Q:Ideal O) (P:completedReflectionPool I Q) :
    ringChar (O⧸P.val)≠2 := (Finset.mem_filter.mp P.property).2.2.1

lemma completedReflectionPool_nonresidual (I Q:Ideal O) (P:completedReflectionPool I Q) :
    ¬P.val∣rowResidualPart I Q := (Finset.mem_filter.mp P.property).2.2.2

lemma completedReflectionPool_divides (I Q:Ideal O) (hI:I≠0) (hQ:Q≠0)
    (P:completedReflectionPool I Q) : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1

lemma completedReflectionPool_coprime (I Q:Ideal O) :
    Pairwise (fun P R:completedReflectionPool I Q=>IsCoprime P.val R.val) := by
  let (P:completedReflectionPool I Q):P.val.IsMaximal:=completedReflectionPool_maximal I Q P
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)

theorem completedReflectionPool_eq_on_fiber (I J Q:Ideal O)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q) :
    completedReflectionPool I Q=completedReflectionPool J Q := by
  ext P
  rw [mem_completedReflectionPool I Q P hI hQ,mem_completedReflectionPool J Q P hJ hQ]
  constructor
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivJ,hresJ,_⟩:=nonresidual_prime_transport I J 1 Q P hI hJ hP hA hT hdiv hres
    exact ⟨hP,hdivJ,hgood,hodd,hresJ⟩
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivI,hresI,_⟩:=nonresidual_prime_transport J I 1 Q P hJ hI hP hA.symm hT.symm hdiv hres
    exact ⟨hP,hdivI,hgood,hodd,hresI⟩

lemma completedReflectionPool_exponent_eq (I J F Q:Ideal O)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:completedReflectionPool I Q) :
    completedLocalExponent I F P.val=completedLocalExponent J F P.val := by
  rcases (mem_completedReflectionPool I Q P.val hI hQ).mp P.property with
    ⟨hP,hdiv,_,_,hres⟩
  exact (nonresidual_prime_transport I J F Q P.val hI hJ hP hA hT hdiv hres).2.2

theorem completedBranchScale_eq_on_fiber {ι:Type*} [Fintype ι]
    (K X:ℝ) (I J F Q:Ideal O) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:ι→Ideal O) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι→Fin 3) :
    completedBranchScale K X I F Q P e=completedBranchScale K X J F Q P e := by
  have hj:(fun i=>completedLocalExponent I F (P i))=(fun i=>completedLocalExponent J F (P i)):=by
    funext i
    exact completedReflectionPool_exponent_eq I J F Q hI hJ hQ hA hT ⟨P i,hP i⟩
  simp only [completedBranchScale,completedResidualScale_eq_on_fiber K I J Q hA hT,hj]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

def reflectionSixActive (e:Fin 6) : Prop := 3≤e.val

def reflectionSixLabel (e:Fin 6) : Fin 3 := ⟨e.val%3,Nat.mod_lt _ (by decide)⟩

def reflectionSixValid {ι:Type*} (e:ι→Fin 6) : Prop :=
  ∀i,e i=0 ∨ reflectionSixActive (e i)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) : ι→Fin 6 := fun i=>
  if h:i∈x.1 then ⟨3+(x.2 ⟨i,h⟩).val,by have ht:=(x.2 ⟨i,h⟩).isLt; omega⟩ else 0

def reflectionSixSupport (e:ι→Fin 6) : Finset ι :=
  Finset.univ.filter (fun i=>reflectionSixActive (e i))

def decodeReflectionSix (e:ι→Fin 6) : ΣA:Finset ι,A→Fin 3 :=
  ⟨reflectionSixSupport e,fun i=>reflectionSixLabel (e i.val)⟩

omit [Fintype ι] in
lemma reflectionSixActive_encode (x:ΣA:Finset ι,A→Fin 3) (i:ι) :
    reflectionSixActive (encodeReflectionSix x i) ↔ i∈x.1 := by
  by_cases hi:i∈x.1
  · simp [encodeReflectionSix,hi,reflectionSixActive]
  · simp [encodeReflectionSix,hi,reflectionSixActive]

omit [Fintype ι] in
lemma encodeReflectionSix_valid (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixValid (encodeReflectionSix x) := by
  intro i
  by_cases hi:i∈x.1
  · exact Or.inr ((reflectionSixActive_encode x i).mpr hi)
  · left
    simp [encodeReflectionSix,hi]

lemma reflectionSixSupport_encode (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixSupport (encodeReflectionSix x)=x.1 := by
  ext i
  simp only [reflectionSixSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    reflectionSixActive_encode]

lemma encodeReflectionSix_injective :
    Function.Injective (encodeReflectionSix (ι:=ι)) := by
  intro x y hxy
  have hsets:x.1=y.1:=by
    rw [←reflectionSixSupport_encode x,←reflectionSixSupport_encode y,hxy]
  rcases x with ⟨A,e⟩
  rcases y with ⟨B,f⟩
  dsimp only at hsets
  subst B
  congr 1
  funext i
  have he:=congrFun hxy i.val
  simp only [encodeReflectionSix,dif_pos i.property] at he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  exact Nat.add_left_cancel hv

lemma encode_decodeReflectionSix (e:ι→Fin 6) (he:reflectionSixValid e) :
    encodeReflectionSix (decodeReflectionSix e)=e := by
  funext i
  by_cases hi:reflectionSixActive (e i)
  · have him:i∈reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    dsimp only [encodeReflectionSix, decodeReflectionSix]
    rw [dif_pos him]
    apply Fin.ext
    change 3 + (e i).val % 3 = (e i).val
    have hl:=(e i).isLt
    dsimp only [reflectionSixActive] at hi
    omega
  · have him:i∉reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    have hz:e i=0:=(he i).resolve_right hi
    simp [encodeReflectionSix,decodeReflectionSix,him,hz]

lemma decode_encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) :
    decodeReflectionSix (encodeReflectionSix x)=x :=
  encodeReflectionSix_injective (encode_decodeReflectionSix _ (encodeReflectionSix_valid x))

def reflectionSixEquiv : (ΣA:Finset ι,A→Fin 3) ≃ {e:ι→Fin 6 // reflectionSixValid e} where
  toFun x:=⟨encodeReflectionSix x,encodeReflectionSix_valid x⟩
  invFun e:=decodeReflectionSix e.val
  left_inv:=decode_encodeReflectionSix
  right_inv e:=Subtype.ext (encode_decodeReflectionSix e.val e.property)

theorem sum_active_exceptional_eq_six {V:Type*} [AddCommMonoid V]
    (F:∀A:Finset ι,(A→Fin 3)→V) :
    (∑A:Finset ι,∑e:A→Fin 3,F A e)=
      ∑e:ι→Fin 6,if reflectionSixValid e then
        F (decodeReflectionSix e).1 (decodeReflectionSix e).2 else 0 := by
  have he:=Equiv.sum_comp (reflectionSixEquiv (ι:=ι))
    (fun e:{e:ι→Fin 6 // reflectionSixValid e}=>
      F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2)
  have hs:(∑x:ΣA:Finset ι,A→Fin 3,F x.1 x.2)=
      ∑e:{e:ι→Fin 6 // reflectionSixValid e},F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2 := by
    calc
      _=∑x:ΣA:Finset ι,A→Fin 3,
          F (decodeReflectionSix (encodeReflectionSix x)).1
            (decodeReflectionSix (encodeReflectionSix x)).2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact (congrArg (fun y:ΣA:Finset ι,A→Fin 3=>F y.1 y.2)
          (decode_encodeReflectionSix x)).symm
      _=_ := he
  rw [Fintype.sum_sigma] at hs
  rw [hs,←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter reflectionSixValid)
    (by simp) (fun e:ι→Fin 6=>F (decodeReflectionSix e).1 (decodeReflectionSix e).2)).symm

end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

def pool (I Q Q0:Ideal O) : Finset (Ideal O) :=
  (completedReflectionPool I Q).filter (fun P=>¬Q0≤P)

lemma pool_subset (I Q Q0:Ideal O) : pool I Q Q0⊆completedReflectionPool I Q :=
  Finset.filter_subset _ _
lemma pool_maximal (I Q Q0:Ideal O) (P:pool I Q Q0) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_good (I Q Q0:Ideal O) (P:pool I Q Q0) : lambda∉P.val :=
  completedReflectionPool_good I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_odd (I Q Q0:Ideal O) (P:pool I Q Q0) : ringChar (O⧸P.val)≠2 :=
  completedReflectionPool_odd I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_divides (I Q Q0:Ideal O) (hI:I≠0) (hQ:Q≠0) (P:pool I Q Q0) : P.val∣I*Q :=
  completedReflectionPool_divides I Q hI hQ ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_nonresidual (I Q Q0:Ideal O) (P:pool I Q Q0) : ¬P.val∣rowResidualPart I Q :=
  completedReflectionPool_nonresidual I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_free (I Q Q0:Ideal O) (P:pool I Q Q0) : ¬Q0≤P.val :=
  (Finset.mem_filter.mp P.property).2

lemma pool_eq_on_fiber (I J Q Q0:Ideal O) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J) (hT:rowMaskPart I Q=rowMaskPart J Q) :
    pool I Q Q0=pool J Q Q0 := by
  unfold pool
  rw [completedReflectionPool_eq_on_fiber I J Q hI hJ hQ hA hT]


def reflectionChoiceValue (I Q Q0:Ideal O) (e:pool I Q Q0→Fin 6)
    (P:Ideal O) : Fin 6 :=
  if h:P∈pool I Q Q0 then e ⟨P,h⟩ else 0

def reflectionActivePool (I Q Q0:Ideal O) (e:pool I Q Q0→Fin 6) : Finset (Ideal O) :=
  (pool I Q Q0).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q Q0 e P))

lemma reflectionActivePool_subset (I Q Q0:Ideal O) (e:pool I Q Q0→Fin 6) :
    reflectionActivePool I Q Q0 e⊆pool I Q Q0 := Finset.filter_subset _ _

lemma mem_reflectionActivePool (I Q Q0:Ideal O) (e:pool I Q Q0→Fin 6)
    (P:pool I Q Q0) :
    P.val∈reflectionActivePool I Q Q0 e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dif_pos P.property]

lemma reflectionActivePool_encode (I Q Q0:Ideal O)
    (A:Finset (pool I Q Q0)) (e:A→Fin 3) :
    reflectionActivePool I Q Q0 (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:pool I Q Q0:=⟨P,reflectionActivePool_subset I Q Q0 _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q Q0 _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q Q0 _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)

def reflectionActiveLabel (I Q Q0:Ideal O) (e:pool I Q Q0→Fin 6)
    (P:reflectionActivePool I Q Q0 e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩)

end CompletedGauss.FreeReflection

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

def dualIdealDyad (j : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo ∅ (2^j)).filter
    (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

lemma mem_dualIdealDyad (I : Ideal O) (j : ℕ) :
    I∈dualIdealDyad j ↔ I≠0 ∧ Nat.clog 2 (Ideal.absNorm I)=j := by
  simp only [dualIdealDyad,Finset.mem_filter,mem_outsideIdealsUpTo,
    Finset.notMem_empty,false_implies,forall_const,and_true]
  constructor
  · rintro ⟨⟨hI,_⟩,hj⟩
    exact ⟨fun h => by simp [h] at hI,hj⟩
  · rintro ⟨hI,hj⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩,hj⟩
    simpa only [hj] using Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)

lemma dualIdealDyad_bounds (j : ℕ) (I : Ideal O) (hI : I∈dualIdealDyad j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hn,hj⟩:= (mem_dualIdealDyad I j).mp hI
  have hu:=Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl:=two_pow_clog_le_double (Ideal.absNorm I)
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn))
  rw [hj] at hu hl
  refine ⟨hn,?_,by exact_mod_cast hu⟩
  have he : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ):=by exact_mod_cast hl
  linarith

abbrev NonzeroDualIdeal := {I : Ideal O // I≠0}

def dualDyadicIndexEquiv :
    (ℕ×NonzeroDualIdeal×NonzeroDualIdeal) ≃
      (Σ i : ℕ×ℕ×ℕ, (dualIdealDyad i.2.2)×(dualIdealDyad i.2.1)) where
  toFun x := ⟨(x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val)),
    ⟨⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩,
      ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩⟩⟩
  invFun x := ⟨x.1.1,⟨x.2.1.val,((mem_dualIdealDyad _ _).mp x.2.1.property).1⟩,
    ⟨x.2.2.val,((mem_dualIdealDyad _ _).mp x.2.2.property).1⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨m,j,k⟩,⟨⟨I,hI⟩,⟨J,hJ⟩⟩⟩
    have hi:=((mem_dualIdealDyad I k).mp hI).2
    have hj:=((mem_dualIdealDyad J j).mp hJ).2
    dsimp only
    subst k
    subst j
    rfl

theorem tsum_dualIdealDyads
    (f : ℕ×NonzeroDualIdeal×NonzeroDualIdeal → ℂ) (hf : Summable f) :
    (∑'x, f x) = ∑'i : ℕ×ℕ×ℕ,
      ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
        f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  let g := f ∘ dualDyadicIndexEquiv.symm
  have hg : Summable g := dualDyadicIndexEquiv.symm.summable_iff.mpr hf
  calc
    _ = ∑'x,g x := (dualDyadicIndexEquiv.symm.tsum_eq f).symm
    _ = ∑'i,∑'x,g ⟨i,x⟩ := Summable.tsum_sigma' (fun _=>hasSum_fintype _ |>.summable) hg
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype,Fintype.sum_prod_type]
      rfl

end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

def sixReflectedBranch (I F Q Q0:Ideal O) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6)
    (amplitude:ℕ→Ideal O→Ideal O→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q Q0 e
  maximal:=fun P=>pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  good:=fun P=>pool_good I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
    let : R.val.IsMaximal:=pool_maximal I Q Q0 ⟨R.val,reflectionActivePool_subset I Q Q0 e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>pool_divides I Q Q0 hI hQ ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  nonresidual:=fun P=>pool_nonresidual I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  label:=reflectionActiveLabel I Q Q0 e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k

end CompletedGauss.FreeReflection

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The signed divisor expansion is the product of local reflected brackets. -/
theorem fixedCuspDivisorSeries_eq_bracket_tsum {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (j : ι→ℕ)
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0<X) :
    fixedCuspDivisorSeries p hg N c s b j V X=
      ∑'h : O,(fixedCuspPeriodicArray N c s b h*
        paperKernel V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)*sourceCuspRadialLength h))*
        ∏i,finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) h) := by
  let R := fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)
  have hR : 0<R := by
    dsimp only [R]
    rw [←fixedCuspReflectionScale_prime_product p s c X]
    exact fixedCuspReflectionScale_pos s _
      (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))) X hX
  let a : O→ℂ := fun h => fixedCuspPeriodicArray N c s b h*paperKernel V (R*sourceCuspRadialLength h)
  have ha : Summable (fun h => ‖a h‖) :=
    fixedCuspPeriodicArray_kernel_norm_summable N c s b V A B hA hs hV R hR
  symm
  change (∑'h : O,a h*∏i,finiteReflectionBracket
    (complexSexticChar (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk (Ideal.span {p i}) h))=_
  rw [tsum_finiteReflectionBracket_divisor_blocks _ j a ha]
  unfold fixedCuspDivisorSeries
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [a,R]
  simp only [mul_assoc]
  rw [fixedCuspPeriodicArray_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]

theorem fixedCuspDivisorSeries_eq_full_brackets {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (j : ι→ℕ)
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0<X) :
    fixedCuspDivisorSeries p hg N c s b j V X=
      ∑'q : ThetaFullIndex,(fixedCuspPeriodicArray N c s b (thetaFullFrequency q)*
        paperKernel V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)*
          (‖ringComplex lambda‖^(2*q.2.1)*completedMellinLength q.2.2)))*
        ∏i,finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (thetaFullFrequency q)) := by
  rw [fixedCuspDivisorSeries_eq_bracket_tsum p hp hg N c hc s b j V A B hA hs hV X hX]
  simp only [mul_assoc]
  rw [fixedCuspPeriodicArray_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical

def ramifiedResidueUnit (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) (u : Oˣ) (m : ℕ) : (O⧸P)ˣ :=
  Units.map (Ideal.Quotient.mk P).toMonoidHom u*
    (Units.mk0 (Ideal.Quotient.mk P lambda) (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)))^m

lemma ramifiedResidueUnit_coe (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) (u : Oˣ) (m : ℕ) :
    (ramifiedResidueUnit P hg u m:O⧸P)=Ideal.Quotient.mk P ((u:O)*lambda^m) := by
  change Ideal.Quotient.mk P (u:O)*(Ideal.Quotient.mk P lambda)^m=_
  rw [map_mul,map_pow]

def ramifiedBracketPhase {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ℂ :=
  ∏i,finiteReflectionUnitFactor (complexSexticChar (P i) (hg i)) (j i)
    (ramifiedResidueUnit (P i) (hg i) u m)

lemma ramifiedBracketPhase_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ‖ramifiedBracketPhase P hg j u m‖=1 := by
  simp only [ramifiedBracketPhase,norm_prod,finiteReflectionUnitFactor_norm,Finset.prod_const_one]

/-- Unit and ramified powers contribute only a norm-one phase independent of the two good ideals. -/
theorem prod_bracket_extract_ramified {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (hj : ∀i,j i<6) (u : Oˣ) (m : ℕ) (n b : O) :
    (∏i,bracket (complexSexticChar (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) (((u:O)*lambda^m)*n*b^3)))=
      ramifiedBracketPhase P hg j u m*
        ∏i,bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)) := by
  have he (i : ι) : bracket (complexSexticChar (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) (((u:O)*lambda^m)*n*b^3))=
      finiteReflectionUnitFactor (complexSexticChar (P i) (hg i)) (j i)
        (ramifiedResidueUnit (P i) (hg i) u m)*
          bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)) := by
    rw [show ((u:O)*lambda^m)*n*b^3=((u:O)*lambda^m)*(n*b^3) by ring,
      map_mul,←ramifiedResidueUnit_coe]
    exact bracket_unit_mul _ (complexSexticChar_powers (P i) (hg i)).2.2 _ (hj i) _ _
  simp only [he,Finset.prod_mul_distrib,ramifiedBracketPhase]

lemma bracket_one_eq_quadratic (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) (x : O⧸P) :
    bracket (complexSexticChar P hg) 1 x=complexQuadraticChar P x := by
  change ((complexSexticChar P hg^3)⁻¹) x=complexQuadraticChar P x
  rw [(complexSexticChar_powers P hg).2.1,complexQuadraticChar_inv]

lemma complexQuadraticChar_cube (P : Ideal O) [P.IsMaximal] (x : O⧸P) :
    complexQuadraticChar P x^3=complexQuadraticChar P x := by
  by_cases hx : x=0
  · rw [hx,MulChar.map_zero,zero_pow (by decide : (3:ℕ)≠0)]
  · have hs : complexQuadraticChar P x^2=1 := by
      change (quadraticChar (O⧸P) x:ℂ)^2=1
      exact_mod_cast quadraticChar_sq_one hx
    rw [pow_succ,hs,one_mul]

lemma bracket_one_cube (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) (n b : O) :
    bracket (complexSexticChar P hg) 1 (Ideal.Quotient.mk P (n*b^3))=
      complexQuadraticChar P (Ideal.Quotient.mk P n)*complexQuadraticChar P (Ideal.Quotient.mk P b) := by
  rw [bracket_one_eq_quadratic,map_mul,map_pow,map_mul,map_pow,complexQuadraticChar_cube]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical

/-- Every residual prime contributes the two canonical quadratic rows. -/
lemma residual_bracket_product (I : Ideal O) (hI : quadraticIdealAdmissible I) (n b : O) :
    letI : ∀P : primeSupport I,P.val.IsMaximal := fun P=>(quadraticIdealPrimeIndex ⟨I,hI⟩ P).property.1
    (∏P : primeSupport I,bracket
      (complexSexticChar P.val (quadraticIdealPrimeIndex ⟨I,hI⟩ P).property.2.1) 1
      (Ideal.Quotient.mk P.val (n*b^3)))=
      canonicalQuadraticRowOfIdeal I n*canonicalQuadraticRowOfIdeal I b := by
  letI : ∀P : primeSupport I,P.val.IsMaximal := fun P=>(quadraticIdealPrimeIndex ⟨I,hI⟩ P).property.1
  simp only [bracket_one_cube,Finset.prod_mul_distrib,
    canonicalQuadraticRowOfIdeal_eq_prime_product I hI]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Normalization transfers the local Gauss sizes from the brackets into one bounded scalar. -/
theorem fixedCuspDivisorSeries_normalized {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (j : ι→ℕ) (hj : ∀i,j i<6)
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0<X) (β : ℂ) :
    β*fixedCuspDivisorSeries p hg N c s b j V X=
      (β/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*
      ∑'q : ThetaFullIndex,(fixedCuspPeriodicArray N c s b (thetaFullFrequency q)*
        paperKernel V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)*
          (‖ringComplex lambda‖^(2*q.2.1)*completedMellinLength q.2.2)))*
        ∏i,bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (thetaFullFrequency q)) := by
  rw [fixedCuspDivisorSeries_eq_full_brackets p hp hg N c hc s b j V A B hA hs hV X hX,
    ←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro q
  rw [←gaussScale_mul_prod (fun i=>O⧸Ideal.span {p i})
    (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
    (fun i=>(complexSexticChar_powers (Ideal.span {p i}) (hg i)).2.2) j hj]
  have hn : (gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (gaussScale_pos _ j).ne'
  field_simp

lemma completedRamifiedStep_pow (m : ℕ) :
    completedRamifiedStep^m=(3:ℝ)^((m:ℝ)/3) := by
  rw [completedRamifiedStep,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma completedRamifiedStep_cube (m : ℕ) :
    (completedRamifiedStep^m)^3=(3:ℝ)^m := by
  rw [completedRamifiedStep_pow,←Real.rpow_mul_natCast (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [show ((m:ℝ)/3)*(3:ℝ)=m by ring,Real.rpow_natCast]

lemma completedCuspArrayWeight_step (m : ℕ) (I J : Ideal O) :
    completedCuspArrayWeight m I J=
      completedRamifiedStep^m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ) := by
  rw [completedCuspArrayWeight,completedRamifiedStep_pow]

/-- The normalized Fourier coefficient separates ramified phases from the two ideal columns. -/
theorem fixedCuspBracketTerm_normalized {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (hj : ∀i,j i<6)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O) (h : completedCuspArrayEligible I J) :
    fixedCuspPeriodicArray N c s b (completedCuspArrayIndex u m I J)*
      (∏i,bracket (complexSexticChar (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (completedCuspArrayIndex u m I J)))=
      (completedCuspArrayConstant s:ℂ)*ramifiedBracketPhase P hg j u m*
        (completedCuspArray N c s b u m I J*
          ∏i,bracket (complexSexticChar (P i) (hg i)) (j i)
            (Ideal.Quotient.mk (P i) (primaryIdealGenerator I*(primaryIdealGenerator J)^3)))/
        (completedRamifiedStep^m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ) := by
  rw [completedCuspArray_reconstruct N c s b u m I J h]
  simp only [completedCuspArrayIndex]
  rw [prod_bracket_extract_ramified P hg j hj,completedCuspArrayWeight_step]
  ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

def nonzeroDualDilation (D E:Ideal O) (hD:D≠0) (hE:E≠0)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℕ×NonzeroDualIdeal×NonzeroDualIdeal :=
  (x.1,⟨D*x.2.1.val,mul_ne_zero hD x.2.1.property⟩,
    ⟨E*x.2.2.val,mul_ne_zero hE x.2.2.property⟩)

lemma nonzeroDualDilation_injective (D E:Ideal O) (hD:D≠0) (hE:E≠0) :
    Function.Injective (nonzeroDualDilation D E hD hE) := by
  intro x y h
  apply Prod.ext
  · have ht:=congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.1) h
    exact ht
  · apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel₀ hD (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.1.val) h)
    · apply Subtype.ext
      exact mul_left_cancel₀ hE (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.2.val) h)

theorem tsum_nonzeroDualDilation (D E:Ideal O) (hD:D≠0) (hE:E≠0)
    (f:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ)
    (hsupport:∀x,f x≠0 → D∣x.2.1.val ∧ E∣x.2.2.val) :
    (∑'x,f x)=∑'x,f (nonzeroDualDilation D E hD hE x) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun x:Function.support (fun y=>f (nonzeroDualDilation D E hD hE y))=>
      nonzeroDualDilation D E hD hE x.val)
  · exact (nonzeroDualDilation_injective D E hD hE).comp Subtype.val_injective
  · intro x hx
    obtain ⟨hn,hb⟩:=hsupport x hx
    obtain ⟨n,hn⟩:=hn
    obtain ⟨b,hb⟩:=hb
    have hn0:n≠0:=by
      intro hz
      apply x.2.1.property
      rw [hn,hz,mul_zero]
    have hb0:b≠0:=by
      intro hz
      apply x.2.2.property
      rw [hb,hz,mul_zero]
    let y:ℕ×NonzeroDualIdeal×NonzeroDualIdeal:=(x.1,⟨n,hn0⟩,⟨b,hb0⟩)
    have hy:nonzeroDualDilation D E hD hE y=x:=by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact Subtype.ext hn.symm
        · exact Subtype.ext hb.symm
    refine ⟨⟨y,?_⟩,hy⟩
    change f (nonzeroDualDilation D E hD hE y)≠0
    rwa [hy]
  · intro x
    rfl

lemma completedCuspArray_nonzero (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (m : ℕ) (I J : Ideal O)
    (hne : completedCuspArray N c s b u m I J≠0) : completedCuspArrayEligible I J := by
  by_contra h
  exact hne (by simp only [completedCuspArray,if_neg h])

/-- Nonzero branch terms force exactly the two extracted ideal divisors. -/
lemma completedCuspBranch_support {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k=>IsCoprime (P i) (P k))) (j : ι→ℕ) (e : ι→Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O)
    (hne : completedCuspArray N c s b u m I J*
      reflectedBranch P hg j e (primaryIdealGenerator I) (primaryIdealGenerator J)≠0) :
    reflectionExtractedDivisor P j e 1∣I ∧ reflectionExtractedDivisor P j e 2∣J := by
  obtain ⟨ha,hb⟩:=mul_ne_zero_iff.mp hne
  have he:=completedCuspArray_nonzero N c s b u m I J ha
  have hd:=reflectedBranch_divisibility P hg hcop j e
    (primaryIdealGenerator I) (primaryIdealGenerator J) hb
  rw [(primaryIdealGenerator_spec I he.2.1).1,(primaryIdealGenerator_spec J he.2.2).1] at hd
  exact ⟨hd.1,hd.2.1⟩

/-- The full ideal sum may be reindexed by the forced branch divisors. -/
theorem completedCuspBranch_tsum_extract {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k=>IsCoprime (P i) (P k))) (j : ι→ℕ) (e : ι→Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (kernel : (ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    let hD:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 1
    let hE:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 2
    (∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      (completedCuspArray N c s b u x.1 x.2.1.val x.2.2.val*
        reflectedBranch P hg j e (primaryIdealGenerator x.2.1.val) (primaryIdealGenerator x.2.2.val))*kernel x)=
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      (completedCuspArray N c s b u x.1 (D*x.2.1.val) (E*x.2.2.val)*
        reflectedBranch P hg j e (primaryIdealGenerator (D*x.2.1.val))
          (primaryIdealGenerator (E*x.2.2.val)))*kernel (nonzeroDualDilation D E hD hE x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  exact completedCuspBranch_support P hg hcop j e N c s b u x.1 x.2.1.val x.2.2.val
    (mul_ne_zero_iff.mp hx).1

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

abbrev FullDualIdealIndex := Oˣ×ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def thetaFullToDual (q : ThetaFullIndex) : FullDualIdealIndex :=
  (q.1,q.2.1,⟨q.2.2.1.val,primaryIdealGenerator_ne_zero_ideal _ q.2.2.1.property.2⟩,
    ⟨q.2.2.2.val,primaryIdealGenerator_ne_zero_ideal _ q.2.2.2.property⟩)

lemma thetaFullToDual_injective : Function.Injective thetaFullToDual := by
  intro x y h
  refine Prod.ext ?_ ?_
  · exact congrArg (fun q : FullDualIdealIndex=>q.1) h
  refine Prod.ext ?_ ?_
  · exact congrArg (fun q : FullDualIdealIndex=>q.2.1) h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun q : FullDualIdealIndex=>q.2.2.1.val) h)
  · exact Subtype.ext (congrArg (fun q : FullDualIdealIndex=>q.2.2.2.val) h)

/-- Extending the squarefree-primary coefficients by zero leaves their infinite sum unchanged. -/
theorem tsum_thetaFull_zero_extension (f : FullDualIdealIndex→ℂ)
    (hsupport : ∀x,f x≠0→completedCuspArrayEligible x.2.2.1.val x.2.2.2.val) :
    (∑'x,f x)=∑'q : ThetaFullIndex,f (thetaFullToDual q) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun q : Function.support (fun q : ThetaFullIndex=>f (thetaFullToDual q))=>thetaFullToDual q.val)
  · exact thetaFullToDual_injective.comp Subtype.val_injective
  · intro x hx
    have he:=hsupport x hx
    let q : ThetaFullIndex:=(x.1,x.2.1,⟨x.2.2.1.val,he.1,he.2.1⟩,⟨x.2.2.2.val,he.2.2⟩)
    have hq : thetaFullToDual q=x := rfl
    refine ⟨⟨q,?_⟩,hq⟩
    change f (thetaFullToDual q)≠0
    rwa [hq]
  · intro q
    rfl

theorem completedCuspArray_tsum_zero_extension
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (kernel : FullDualIdealIndex→ℂ) :
    (∑'x : FullDualIdealIndex,
      completedCuspArray N c s b x.1 x.2.1 x.2.2.1.val x.2.2.2.val*kernel x)=
    ∑'q : ThetaFullIndex,
      completedCuspArray N c s b q.1 q.2.1 q.2.2.1.val q.2.2.2.val*kernel (thetaFullToDual q) := by
  apply tsum_thetaFull_zero_extension
  intro x hx
  exact completedCuspArray_nonzero N c s b x.1 x.2.1 x.2.2.1.val x.2.2.2.val
    (mul_ne_zero_iff.mp hx).1

end CompletedGauss

namespace CompletedGauss
open scoped BigOperators Classical
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def mandatoryActiveEquiv (R:Finset ι) :
    {A:Finset ι // R⊆A}≃Finset {i:ι // i∉R} where
  toFun A:=A.val.subtype (fun i=>i∉R)
  invFun B:=⟨R∪B.image Subtype.val,Finset.subset_union_left⟩
  left_inv A:=by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_subtype]
    constructor
    · rintro (hi|⟨j,hj,rfl⟩)
      · exact A.property hi
      · exact hj
    · intro hi
      by_cases hr:i∈R
      · exact Or.inl hr
      · exact Or.inr ⟨⟨i,hr⟩,hi,rfl⟩
  right_inv B:=by
    ext i
    simp only [Finset.mem_subtype,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (hi|⟨j,hj,hji⟩)
      · exact False.elim (i.property hi)
      · have he:j=i:=Subtype.ext hji
        simpa only [he] using hj
    · intro hi
      exact Or.inr ⟨i,hi,rfl⟩

lemma sum_mandatory_active {V:Type*} [AddCommMonoid V]
    (R:Finset ι) (F:Finset ι→V) (hz:∀A,¬R⊆A→F A=0) :
    (∑A:Finset ι,F A)=
      ∑B:Finset {i:ι // i∉R},F (R∪B.image Subtype.val) := by
  calc
    _=∑A:Finset ι,if R⊆A then F A else 0:=by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases h:R⊆A
      · simp only [if_pos h]
      · simp only [if_neg h,hz A h]
    _=∑A:{A:Finset ι // R⊆A},F A.val:=by
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun A:Finset ι=>R⊆A)) (by simp) F
    _=_:=by
      apply Fintype.sum_equiv (mandatoryActiveEquiv R)
      intro A
      exact congrArg F (congrArg Subtype.val ((mandatoryActiveEquiv R).left_inv A)).symm

theorem inactive_weight_mandatory_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)*
          F (R∪B.image Subtype.val) := by
  apply sum_mandatory_active R
  intro A hA
  have hex:∃i∈R,i∉A:=by
    by_contra! hn
    exact hA hn
  obtain ⟨i,hi,hni⟩:=hex
  have hm:i∈(Finset.univ:Finset ι)\A:=by simp [hni]
  rw [Finset.prod_eq_zero hm (hz i hi),zero_mul]

lemma inactive_product_complement (R:Finset ι) (z:ι→ℂ)
    (B:Finset {i:ι // i∉R}) :
    (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)=
      ∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val := by
  symm
  apply Finset.prod_bij (fun i _=>i.val)
  · intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hi ⊢
    intro hmem
    rcases Finset.mem_union.mp hmem with hr|hb
    · exact i.property hr
    · obtain ⟨j,hj,hji⟩:=Finset.mem_image.mp hb
      exact hi ((Subtype.ext hji) ▸ hj)
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    have hnot:i∉R∪B.image Subtype.val:=(Finset.mem_sdiff.mp hi).2
    have hr:i∉R:=fun h=>hnot (Finset.mem_union_left _ h)
    refine ⟨⟨i,hr⟩,?_,rfl⟩
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro hb
    exact hnot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i,hr⟩,hb,rfl⟩))
  · intro i hi
    rfl

theorem inactive_weight_optional_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val)*
          F (R∪B.image Subtype.val) := by
  rw [inactive_weight_mandatory_active R z hz F]
  apply Finset.sum_congr rfl
  intro B hB
  rw [inactive_product_complement]

end CompletedGauss

namespace CompletedGauss
open Eisenstein NormalizedReflection
open scoped BigOperators Classical
variable {α β:Type*} [Fintype α] [Fintype β]

def residualZeroLabel (e:β→Fin 3) : α⊕β→Fin 3 := Sum.elim (fun _=>0) e

theorem sum_labels_drop_residual (f:(α⊕β→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (Sum.inl i)≠0)→f e=0) :
    (∑e:α⊕β→Fin 3,f e)=∑e:β→Fin 3,f (residualZeroLabel e) := by
  rw [←(Equiv.sumArrowEquivProdArrow α β (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single (fun _ : α=>0)]
  · rfl
  · intro d hd hn
    apply hzero
    have hx:∃i:α,d i≠0:=by
      by_contra h
      push_neg at h
      exact hn (funext h)
    obtain ⟨i,hi⟩:=hx
    exact ⟨i,hi⟩
  · simp

lemma reflectedBranch_residual_label_zero
    (P:α⊕β→Ideal O) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (hbad:∃i:α,e (Sum.inl i)≠0) (n b:O) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,if_neg hi]

lemma reflectionExtractedDivisor_drop_residual
    (P:α⊕β→Ideal O) (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j e v=
      reflectionExtractedDivisor (fun i:β=>P (Sum.inr i)) (fun i=>j (Sum.inr i))
        (fun i=>e (Sum.inr i)) v := by
  simp only [reflectionExtractedDivisor,Fintype.prod_sum_type]
  have hz:(∏i:α,reflectionExtractedPrime (P (Sum.inl i)) (j (Sum.inl i)) (e (Sum.inl i)) v)=1 := by
    simp only [hj,reflectionExtractedPrime,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,
      false_and,false_or,ite_false,Finset.prod_const_one]
  rw [hz,one_mul]

lemma reflectedBranch_drop_residual
    (P:α⊕β→Ideal O) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:β→Fin 3) (n b:O) :
    reflectedBranch P hg j (residualZeroLabel e) n b=
      (∏i:α,bracket (complexSexticChar (P (Sum.inl i)) (hg (Sum.inl i))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (Sum.inr i)) (fun i=>hg (Sum.inr i))
        (fun i=>j (Sum.inr i)) e n b := by
  simp only [reflectedBranch,Fintype.prod_sum_type,residualZeroLabel,Sum.elim_inl,Sum.elim_inr]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_true]

end CompletedGauss

namespace CompletedGauss
open Eisenstein NormalizedReflection
open scoped BigOperators Classical
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]

def residualLabelVia (E:α⊕β≃ι) (e:β→Fin 3) : ι→Fin 3 :=
  residualZeroLabel e ∘ E.symm

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma residualLabelVia_apply (E:α⊕β≃ι) (e:β→Fin 3) (i:α⊕β) :
    residualLabelVia E e (E i)=residualZeroLabel e i := by
  simp only [residualLabelVia,Function.comp_apply,Equiv.symm_apply_apply]

theorem sum_labels_drop_residual_equiv (E:α⊕β≃ι) (f:(ι→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0) :
    (∑e:ι→Fin 3,f e)=∑e:β→Fin 3,f (residualLabelVia E e) := by
  let e:=Equiv.arrowCongr E (Equiv.refl (Fin 3))
  rw [←e.sum_comp f]
  apply sum_labels_drop_residual
  intro l hl
  apply hzero
  obtain ⟨i,hi⟩:=hl
  refine ⟨i,?_⟩
  simpa only [e,Equiv.arrowCongr_apply,Function.comp_apply,Equiv.refl_apply,Equiv.symm_apply_apply] using hi

omit [Fintype α] [Fintype β] in
lemma reflectedBranch_residual_zero_equiv (E:α⊕β≃ι)
    (P:ι→Ideal O) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0) (n b:O) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (E (Sum.inl i)))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,if_neg hi]

lemma reflectionExtractedDivisor_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal O) (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j (residualLabelVia E e) v=
      reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e v := by
  calc
    _=reflectionExtractedDivisor (fun i=>P (E i)) (fun i=>j (E i)) (residualZeroLabel e) v := by
      unfold reflectionExtractedDivisor
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectionExtractedDivisor_drop_residual _ _ hj _ _

lemma reflectedBranch_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal O) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (n b:O) :
    reflectedBranch P hg j (residualLabelVia E e) n b=
      (∏i:α,bracket (complexSexticChar (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
        (fun i=>j (E (Sum.inr i))) e n b := by
  calc
    _=reflectedBranch (fun i=>P (E i)) (fun i=>hg (E i)) (fun i=>j (E i)) (residualZeroLabel e) n b := by
      unfold reflectedBranch
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectedBranch_drop_residual _ _ _ hj _ _ _

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

def idealInactiveWeight (P : Ideal O) (j : ℕ) : ℂ :=
  if j=0 then 1-(Ideal.absNorm P:ℂ)⁻¹ else 0

lemma idealInactiveWeight_norm (P : Ideal O) (hP : P≠0) (j : ℕ) :
    ‖idealInactiveWeight P j‖≤1 := by
  by_cases hj : j=0
  · rw [idealInactiveWeight,if_pos hj]
    have hq : 1≤(Ideal.absNorm P:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP)
    have hn : 0≤1-(Ideal.absNorm P:ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hq)
    have he : 1-(Ideal.absNorm P:ℂ)⁻¹=((1-(Ideal.absNorm P:ℝ)⁻¹:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_of_nonneg hn]
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  · simp only [idealInactiveWeight,if_neg hj,norm_zero,zero_le_one]

lemma finiteAdditiveFourier_sextic_zero_ideal (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (ho : ringChar (O⧸P)≠2) (ψ : AddChar (O⧸P) ℂ)
    (j : ℕ) (hj : j<6) :
    finiteAdditiveFourierCoeff ψ (complexSexticChar P hg^j : MulChar (O⧸P) ℂ) 0=
      idealInactiveWeight P j := by
  rw [finiteAdditiveFourier_sextic_zero P hg ho ψ j hj]
  have he : Fintype.card (O⧸P)=Ideal.absNorm P := by rw [←Nat.card_eq_fintype_card]; rfl
  rw [he,idealInactiveWeight]
  split_ifs
  · have hn : (Ideal.absNorm P:ℂ)≠0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne P)
    field_simp
  · rfl

def primeInactiveFourierWeight {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (j : ι→ℕ) (A : Finset ι) : ℂ :=
  ∏i : {i // i∉A},finiteAdditiveFourierCoeff
    (residueTraceQuotientChar 1 (p i.val) (hp i.val))
    (complexSexticChar (Ideal.span {p i.val}) (hg i.val)^j i.val : MulChar (O⧸Ideal.span {p i.val}) ℂ) 0

lemma primeInactiveFourierWeight_formula {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (ho : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (A : Finset ι) :
    primeInactiveFourierWeight p hp hg j A=
      ∏i∈(Finset.univ:Finset ι)\A,idealInactiveWeight (Ideal.span {p i}) (j i) := by
  unfold primeInactiveFourierWeight
  simp only [finiteAdditiveFourier_sextic_zero_ideal _ _ (ho _) _ _ (hj _)]
  exact (Finset.prod_subtype ((Finset.univ:Finset ι)\A)
    (p := fun i=>i∉A)
    (by intro i; simp only [Finset.mem_sdiff,Finset.mem_univ,true_and])
    (fun i=>idealInactiveWeight (Ideal.span {p i}) (j i))).symm

namespace FreeReflection

def reflectionInactiveStratumWeight (I F Q Q0 : Ideal O) (A : Finset (pool I Q Q0)) : ℂ :=
  ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,idealInactiveWeight P.val (completedLocalExponent I F P.val)

lemma reflectionInactiveStratumWeight_norm (I F Q Q0 : Ideal O) (A : Finset (pool I Q Q0)) :
    ‖reflectionInactiveStratumWeight I F Q Q0 A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one
  · intro P hP
    exact norm_nonneg _
  · intro P hP
    letI : P.val.IsMaximal:=pool_maximal I Q Q0 P
    exact idealInactiveWeight_norm _ (NeZero.ne _) _

end FreeReflection
end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical

lemma actual_bracket_ideal_congr (P R : Ideal O) [P.IsMaximal] [R.IsMaximal]
    (hP : lambda∉P) (hR : lambda∉R) (he : P=R) (j : ℕ) (z : O) :
    bracket (complexSexticChar P hP) j (Ideal.Quotient.mk P z)=
      bracket (complexSexticChar R hR) j (Ideal.Quotient.mk R z) := by
  subst R
  rfl

lemma reflectedLocalPiece_ideal_congr (P R : Ideal O) [P.IsMaximal] [R.IsMaximal]
    (hP : lambda∉P) (hR : lambda∉R) (he : P=R) (j : ℕ) (e : Fin 3) (n b : O) :
    reflectedLocalPiece P hP j e n b=reflectedLocalPiece R hR j e n b := by
  subst R
  rfl

/-- Reindexing the active primes separates the residual quadratic character from the fixed branch. -/
theorem reflectedBranch_residual_coefficient {ι β : Type*} [Fintype ι] [Fintype β]
    (k : Ideal O) (hk : quadraticIdealAdmissible k)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (E : primeSupport k⊕β≃ι)
    (hres : ∀r,P (E (Sum.inl r))=r.val) (hnonres : ∀r,P (E (Sum.inr r))=R r)
    (j : ι→ℕ) (l : β→ℕ) (hjres : ∀r,j (E (Sum.inl r))=1)
    (hjnonres : ∀r,j (E (Sum.inr r))=l r) (e : β→Fin 3) (n b : O) :
    reflectedBranch P hg j (residualLabelVia E e) n b=
      (canonicalQuadraticRowOfIdeal k n*canonicalQuadraticRowOfIdeal k b)*
        reflectedBranch R hR l e n b := by
  rw [reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hquad : (∏r : primeSupport k,
      bracket (complexSexticChar (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1
        (Ideal.Quotient.mk _ (n*b^3)))=
      canonicalQuadraticRowOfIdeal k n*canonicalQuadraticRowOfIdeal k b := by
    letI : ∀r : primeSupport k,r.val.IsMaximal:=fun r=>(quadraticIdealPrimeIndex ⟨k,hk⟩ r).property.1
    calc
      _=∏r : primeSupport k,bracket
          (complexSexticChar r.val (quadraticIdealPrimeIndex ⟨k,hk⟩ r).property.2.1) 1
            (Ideal.Quotient.mk r.val (n*b^3)) := by
        apply Finset.prod_congr rfl
        intro r hr
        exact actual_bracket_ideal_congr _ _ _ _ (hres r) 1 (n*b^3)
      _=_:=residual_bracket_product k hk n b
  rw [hquad]
  congr 1
  unfold reflectedBranch
  apply Finset.prod_congr rfl
  intro r hr
  dsimp only
  rw [hjnonres]
  exact reflectedLocalPiece_ideal_congr _ _ _ _ (hnonres r) _ _ _ _

lemma active_product_admissible_equiv {ι β : Type*} [Fintype ι] [Fintype β]
    (k : Ideal O) (hk : Squarefree k) (P : ι→Ideal O) (R : β→Ideal O)
    (E : primeSupport k⊕β≃ι)
    (hres : ∀r,P (E (Sum.inl r))=r.val) (hnonres : ∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=k*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  exact (Finset.prod_coe_sort (primeSupport k) (fun r : Ideal O=>r)).trans
    (squarefree_support_product_self hk)

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical ContDiff

lemma nonzeroDualIdeal_norm_pos (I : NonzeroDualIdeal) :
    0<(Ideal.absNorm I.val:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

lemma nonzeroDualIdeal_inv_pow_summable (n : ℕ) (hn : 1<n) :
    Summable (fun I : NonzeroDualIdeal => ((Ideal.absNorm I.val:ℝ)^n)⁻¹) := by
  have hs := (fullIdealWeight_summable_norm (n:ℂ)
    (by exact_mod_cast hn)).subtype (fun I : Ideal O => I≠0)
  apply hs.congr
  intro I
  simp only [Function.comp_apply,fullIdealWeight,if_neg I.property,
    Complex.cpow_neg,Complex.cpow_natCast,norm_inv,norm_pow,Complex.norm_natCast]

def rawDualKernelTerm (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal O→Ideal O→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * paperKernel V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

lemma rawDualKernel_inverse_square (scale ρ q : ℝ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ =
      (scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹) := by
  simp only [mul_pow,mul_inv_rev,←pow_mul,←inv_pow]
  ring

theorem rawDualKernelTerm_summable_norm
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal O→Ideal O→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=paperKernel_power_bound V a b ha hsupp hV 2
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := hdec _ hx
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖paperKernel V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion CompletedDyadic
open scoped BigOperators Classical ContDiff
section

lemma canonical_dual_kernel_argument (K Y ρ q : ℝ) (i : ℕ×ℕ×ℕ)
    (k n b : Ideal O) (hK : 0<K) (hk : k≠0) (hn : n≠0) (hb : b≠0) :
    (Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
      Real.exp (-2*Real.log ((Ideal.absNorm k:ℝ)/K)+
        Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
        3*Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)) =
    (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2)*(ρ*q^i.1)^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 := by
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  have hnn:=nonzeroDualIdeal_norm_pos ⟨n,hn⟩
  have hbn:=nonzeroDualIdeal_norm_pos ⟨b,hb⟩
  have hrk : 0<(Ideal.absNorm k:ℝ)/K:=div_pos hkn hK
  have hrn : 0<(Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2:=div_pos hnn (by positivity)
  have hrb : 0<(Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1:=div_pos hbn (by positivity)
  rw [show -2*Real.log ((Ideal.absNorm k:ℝ)/K)+Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
      3*Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)=
      -(Real.log ((Ideal.absNorm k:ℝ)/K)+Real.log ((Ideal.absNorm k:ℝ)/K))+
      Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
      (Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)+Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)+
        Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)) by ring]
  simp only [Real.exp_add,Real.exp_neg,Real.exp_log hrk,Real.exp_log hrn,Real.exp_log hrb]
  unfold ramifiedScale
  field_simp


def canonicalRawBranchCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ)
    (η : ℕ→Ideal O→Ideal O→ℂ) (σ : ℕ→ℂ) (k : Ideal O)
    (m : ℕ) (n b : Ideal O) : ℂ :=
  σ m*canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (n*b))*
    reflectedDyadicCoefficient P hg j e (η m) (ramifiedScale ρ q m) n b

lemma canonicalRawBranchCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ) (hρ : 0<ρ) (hq : 1≤q)
    (η : ℕ→Ideal O→Ideal O→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal O) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖canonicalRawBranchCoefficient P hg j e ρ q η σ k m n.val b.val‖≤1/ρ := by
  have hn:=norm_at_least_one n.val n.property
  have hb:=norm_at_least_one b.val b.property
  have hr:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hc:=reflectedDyadicCoefficient_norm P hg j e (η m) (ramifiedScale ρ q m) 1 1
    hr (by norm_num) (by norm_num) n.val b.val n.property b.property (hη m n b)
    (by linarith) (by linarith)
  have hdiv (v : Fin 3) : 1≤(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) :=
    norm_at_least_one _ (reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e v)
  have hroot : 1≤Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [hdiv 0,hdiv 2]
  have hrho : ρ≤ramifiedScale ρ q m := by
    exact le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
  have hden := hrho.trans (le_mul_of_one_le_right hr.le hroot)
  simp only [Real.sqrt_one,one_mul] at hc
  have hcoeff:=hc.trans (div_le_div_of_nonneg_left (by norm_num) hρ hden)
  rw [canonicalRawBranchCoefficient,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (hσ m)).trans (canonicalQuadraticRowOfIdeal_norm_le_one _ _))).trans hcoeff

theorem reflectedBranchBlock_canonical {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (η : ℕ→Ideal O→Ideal O→ℂ) (σ : ℕ→idealRange K→ℂ)
    (i : ℕ×ℕ×ℕ) (k : idealRange K) (hK : 0<K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k =
    ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val)
        (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  have hkm:=mem_idealRange.mp k.property
  have hwk:=completedShellWindow_log (Ideal.absNorm k.val:ℝ) K
    (nonzeroDualIdeal_norm_pos ⟨k.val,hkm.1.2.1.ne_zero⟩) hK hk hkm.2
  simp only [reflectedBranchBlock,completedSmoothDyadicBlock,Finset.mul_sum]
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.2)]
  apply Finset.sum_congr rfl
  intro n _
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.1)]
  apply Finset.sum_congr rfl
  intro b _
  have hn:=dualIdealDyad_bounds _ n.val n.property
  have hb:=dualIdealDyad_bounds _ b.val b.property
  have hwn:=completedShellWindow_log (Ideal.absNorm n.val:ℝ) ((2:ℝ)^i.2.2)
    (nonzeroDualIdeal_norm_pos ⟨n.val,hn.1⟩) (by positivity) hn.2.1 hn.2.2
  have hwb:=completedShellWindow_log (Ideal.absNorm b.val:ℝ) ((2:ℝ)^i.2.1)
    (nonzeroDualIdeal_norm_pos ⟨b.val,hb.1⟩) (by positivity) hb.2.1 hb.2.2
  rw [hwk,hwn,hwb,canonical_dual_kernel_argument K Y ρ q i k.val n.val b.val hK hkm.1.2.1.ne_zero hn.1 hb.1]
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

theorem canonicalRawBranch_summable_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal O→Ideal O→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal O) (hk : k≠0) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η σ k) x‖) := by
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  exact rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) _ ρ q (1/ρ) (by positivity) hρ hq (by positivity)
    _ (fun m n b=>canonicalRawBranchCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ k m n b)

theorem canonical_reflected_series {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal O→Ideal O→ℂ) (σ : ℕ→idealRange K→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m k,‖σ m k‖≤1) (k : idealRange K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    (∑'i : ℕ×ℕ×ℕ, reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k) =
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val) x := by
  have hs:=canonicalRawBranch_summable_norm P hg j e W a b ha hsupp hW K Y ρ q
    hK hY hρ hq η (fun m=>σ m k) hη (fun m=>hσ m k) k.val
    (mem_idealRange.mp k.property).1.2.1.ne_zero
  rw [tsum_dualIdealDyads _ hs.of_norm]
  apply tsum_congr
  intro i
  exact reflectedBranchBlock_canonical P hg j e W K Y ρ q η σ i k hK hk

end

open Eisenstein SchwartzPlanePoisson CanonicalQuadraticSieve CompletedDyadic

namespace ReflectedBranchData

def withCanonicalCuspArray {levelBound K : ℝ} {I F Q : Ideal O}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal O→Ideal O→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  { d with
    nColumns := fun i=>dualIdealDyad i.2.2
    bColumns := fun i=>dualIdealDyad i.2.1
    nBounds := fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
    bBounds := fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
    amplitude := fun i=>η i.1
    amplitude_bound := fun i n hn b hb=>hη i.1
      ⟨n,((mem_dualIdealDyad _ _).mp hn).1⟩ ⟨b,((mem_dualIdealDyad _ _).mp hb).1⟩
    rowPhase := fun i=>σ i.1
    rowPhase_bound := fun i k=>hσ i.1 k }

def rawValue {levelBound K : ℝ} {I F Q : Ideal O}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal O→Ideal O→ℂ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  exact ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    rawDualKernelTerm (Vstar W)
      ((completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2) ρ q
      (canonicalRawBranchCoefficient (fun p : d.primes=>p.val) d.good
        (fun p=>completedLocalExponent I F p.val) d.label ρ q η (fun m=>σ m k) k.val) x

theorem withCanonicalCuspArray_value {levelBound K : ℝ} {I F Q : Ideal O}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal O→Ideal O→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X ρ q : ℝ) (hX : 0<X) (hρ : 0<ρ) (hq : 1<q)
    (hK : 0<completedResidualScale K I Q)
    (k : idealRange (completedResidualScale K I Q))
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withCanonicalCuspArray η hη σ hσ).value W X ρ q k =
      d.rawValue η σ W X ρ q k := by
  let : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) :=
    nonzeroDualIdeal_norm_pos ⟨J,hJ⟩
  have hprod:=hn (∏p : d.primes,p.val)
    (Finset.prod_ne_zero_iff.mpr (fun p _=>NeZero.ne p.val))
  have hd:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 1)
  have he:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 2)
  have hy : 0<completedBranchScale K (X/d.levelScale) I F Q
      (fun p : d.primes=>p.val) d.label := by
    unfold completedBranchScale
    have hl:=d.levelScale_pos
    positivity
  exact canonical_reflected_series (fun p : d.primes=>p.val) d.good
    (fun p=>completedLocalExponent I F p.val) d.label W a b ha hsupp hW
    (completedResidualScale K I Q)
    (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)
    ρ q hK hy hρ hq η σ hη hσ k hk

end ReflectedBranchData
end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion CanonicalQuadraticSieve CompletedDyadic
open scoped BigOperators Classical

def residualArgumentPhase (k D E : Ideal O) : ℂ :=
  canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (D*E))

lemma residualArgumentPhase_norm_le_one (k D E : Ideal O) :
    ‖residualArgumentPhase k D E‖≤1 := canonicalQuadraticRowOfIdeal_norm_le_one _ _

lemma residualArgumentPhase_extract (k D E n b : Ideal O) :
    canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (D*n))*
      canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (E*b))=
      residualArgumentPhase k D E*canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (n*b)) := by
  simp only [residualArgumentPhase,primaryIdealGenerator_mul,canonicalQuadraticRowOfIdeal_mul]
  ring

/-- The extracted ideal divisors enter only a bounded residual row phase. -/
theorem canonicalRawBranchCoefficient_cusp {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : ℕ→Ideal O→Ideal O→ℂ) (σ : ℕ→ℂ)
    (k : Ideal O) (ρ q : ℝ) (m : ℕ) (n b : Ideal O) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    4*canonicalRawBranchCoefficient P hg j e ρ q
      (fun m n b=>η m (D*n) (E*b)) (fun m=>σ m*residualArgumentPhase k D E) k m n b=
      σ m*η m (D*n) (E*b)*
        (canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (D*n))*
          canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (E*b)))*
        reflectedBranch P hg j e (primaryIdealGenerator (D*n)) (primaryIdealGenerator (E*b))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ) := by
  dsimp only
  rw [residualArgumentPhase_extract]
  simp only [canonicalRawBranchCoefficient,reflectedDyadicCoefficient,Complex.ofReal_mul,
    Complex.ofReal_ofNat,div_eq_mul_inv,mul_inv_rev]
  ring

namespace ReflectedBranchData
variable {levelBound K : ℝ} {I F Q : Ideal O}
variable (d : ReflectedBranchData levelBound K I F Q)

def cuspAmplitude (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (m : ℕ) (n v : Ideal O) : ℂ :=
  completedCuspArray N c s b u m
    (reflectionExtractedDivisor (fun p : d.primes=>p.val) (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p : d.primes=>p.val) (fun p=>completedLocalExponent I F p.val) d.label 2*v)

lemma cuspAmplitude_norm (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (m : ℕ) (n v : Ideal O) : ‖d.cuspAmplitude N c s b u m n v‖≤1 :=
  completedCuspArray_norm _ _ _ _ _ _ _ _

/-- The actual cusp coefficient array supplies the bounded columns of a reflected branch. -/
def withCompletedCuspArray (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hσ : ∀m k,‖σ m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.cuspAmplitude N c s b u)
    (fun m n v=>d.cuspAmplitude_norm N c s b u m n.val v.val) σ hσ

end ReflectedBranchData
end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical

def fixedCuspDenominators (c : O) : Finset O :=
  (firstFrequencyDisk (‖ringComplex (9*c)‖^2)).filter (fun d=>d≠0 ∧ d∣9*c)

lemma mem_fixedCuspDenominators (c : O) (hc : c≠0) (d : O) :
    d∈fixedCuspDenominators c ↔ d≠0 ∧ d∣9*c := by
  rw [fixedCuspDenominators,Finset.mem_filter]
  constructor
  · exact fun h=>h.2
  · intro hd
    exact ⟨(mem_firstFrequencyDisk _ _).mpr
      (element_norm_le_of_dvd (mul_ne_zero (by norm_num) hc) hd.2),hd⟩

/-- Fixed cusp data range over finitely many denominators, sectors, residues, and units. -/
abbrev FixedCuspRay (c : O) :=
  (O⧸Ideal.span {9*c})×fixedCuspDenominators c×FixedCuspSector×(O⧸Ideal.span {243*c})×Oˣ

lemma fixedCuspRay_finite (c : O) (hc : c≠0) : Finite (FixedCuspRay c) := by
  letI : Finite Oˣ:=cubic_units_finite
  letI : Finite (O⧸Ideal.span {9*c}):=
    (Ideal.span {9*c}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hc))
  letI : Finite (O⧸Ideal.span {243*c}):=
    (Ideal.span {243*c}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hc))
  infer_instance

def fixedCuspRayLevel (c : O) (r : FixedCuspRay c) : ℝ :=
  (fixedCuspReflectionScale r.2.2.1 r.2.1.val 1)⁻¹

lemma fixedCuspRayLevel_pos (c : O) (hc : c≠0) (r : FixedCuspRay c) :
    0<fixedCuspRayLevel c r :=
  inv_pos.mpr (fixedCuspReflectionScale_pos _ _
    ((mem_fixedCuspDenominators c hc r.2.1.val).mp r.2.1.property).1 1 zero_lt_one)

def fixedCuspLevelBound (c : O) (hc : c≠0) : ℝ := by
  letI : Finite (FixedCuspRay c):=fixedCuspRay_finite c hc
  letI : Fintype (FixedCuspRay c):=Fintype.ofFinite _
  exact 1+∑r : FixedCuspRay c,fixedCuspRayLevel c r

lemma fixedCuspLevelBound_ge_one (c : O) (hc : c≠0) : 1≤fixedCuspLevelBound c hc := by
  letI : Finite (FixedCuspRay c):=fixedCuspRay_finite c hc
  letI : Fintype (FixedCuspRay c):=Fintype.ofFinite _
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun r _=>(fixedCuspRayLevel_pos c hc r).le))

lemma fixedCuspRayLevel_le (c : O) (hc : c≠0) (r : FixedCuspRay c) :
    fixedCuspRayLevel c r≤fixedCuspLevelBound c hc := by
  letI : Finite (FixedCuspRay c):=fixedCuspRay_finite c hc
  letI : Fintype (FixedCuspRay c):=Fintype.ofFinite _
  have h:=Finset.single_le_sum (fun x _=>(fixedCuspRayLevel_pos c hc x).le) (Finset.mem_univ r)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff

lemma thetaFull_radial_length (q : ThetaFullIndex) :
    ‖ringComplex lambda‖^(2*q.2.1)*completedMellinLength q.2.2=
      (completedRamifiedStep^q.2.1)^3*(Ideal.absNorm q.2.2.1.val:ℝ)*(Ideal.absNorm q.2.2.2.val:ℝ)^3 := by
  rw [pow_mul,ringComplex_norm_sq_eq_absNorm_span,absNorm_span_lambda,
    completedMellinLength_eq,completedRamifiedStep_cube]
  push_cast
  ring

def normalizedCuspCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O) : ℂ :=
  ramifiedBracketPhase P hg j u m*completedCuspArray N c s b u m I J*
    (∏i,bracket (complexSexticChar (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) (primaryIdealGenerator I*(primaryIdealGenerator J)^3)))/
    (completedCuspArrayWeight m I J:ℂ)

lemma normalizedCuspCoefficient_nonzero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O)
    (hne : normalizedCuspCoefficient P hg j N c s b u m I J≠0) :
    completedCuspArrayEligible I J := by
  apply completedCuspArray_nonzero N c s b u m I J
  intro hz
  exact hne (by simp only [normalizedCuspCoefficient,hz,mul_zero,zero_mul,zero_div])

/-- The divisor-series reflection is the normalized sum over unrestricted nonzero ideal columns. -/
theorem fixedCuspDivisorSeries_fullDual {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (j : ι→ℕ) (hj : ∀i,j i<6)
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0<X) (β : ℂ) :
    β*fixedCuspDivisorSeries p hg N c s b j V X=
      ((β/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*(completedCuspArrayConstant s:ℂ))*
      ∑'x : FullDualIdealIndex,
        rawDualKernelTerm V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)) 1
          completedRamifiedStep (normalizedCuspCoefficient (fun i=>Ideal.span {p i}) hg j N c s b x.1) x.2 := by
  rw [fixedCuspDivisorSeries_normalized p hp hg N c hc s b j hj V A B hA hs hV X hX β]
  let f : FullDualIdealIndex→ℂ:=fun x=>
    rawDualKernelTerm V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)) 1
      completedRamifiedStep (normalizedCuspCoefficient (fun i=>Ideal.span {p i}) hg j N c s b x.1) x.2
  have hf : (∑'x,f x)=∑'q : ThetaFullIndex,f (thetaFullToDual q) := by
    apply tsum_thetaFull_zero_extension
    intro x hx
    exact normalizedCuspCoefficient_nonzero _ hg j N c s b x.1 x.2.1 x.2.2.1.val x.2.2.2.val
      (mul_ne_zero_iff.mp hx).1
  change _=((β/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*(completedCuspArrayConstant s:ℂ))*(∑'x,f x)
  rw [hf,mul_assoc]
  apply congrArg (fun y : ℂ=>(β/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*y)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro q
  have he:=fixedCuspBracketTerm_normalized (fun i=>Ideal.span {p i}) hg j hj N c s b
    q.1 q.2.1 q.2.2.1.val q.2.2.2.val ⟨q.2.2.1.property.1,q.2.2.1.property.2,q.2.2.2.property⟩
  change fixedCuspPeriodicArray N c s b (thetaFullFrequency q)*
    (∏i,bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (thetaFullFrequency q)))=_ at he
  rw [show (fixedCuspPeriodicArray N c s b (thetaFullFrequency q)*
      paperKernel V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)*
        (‖ringComplex lambda‖^(2*q.2.1)*completedMellinLength q.2.2)))*
      (∏i,bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (thetaFullFrequency q)))=
      (fixedCuspPeriodicArray N c s b (thetaFullFrequency q)*
        (∏i,bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (thetaFullFrequency q))))*
      paperKernel V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)*
        (‖ringComplex lambda‖^(2*q.2.1)*completedMellinLength q.2.2)) by ring,he,thetaFull_radial_length]
  simp only [f,rawDualKernelTerm,thetaFullToDual,normalizedCuspCoefficient,
    completedCuspArrayWeight_step,one_mul]
  simp only [mul_assoc]
  ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff

lemma reflectedLocalSize_pos (P : Ideal O) [P.IsMaximal] (j : ℕ) (e : Fin 3) :
    0<reflectedLocalSize P j e := by
  have hr : 0<rootCard (O⧸P):=rootCard_pos
  unfold reflectedLocalSize
  split_ifs <;> positivity

def bracketProductBound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (j : ι→ℕ) : ℝ :=
  ∏i,∑e : Fin 3,reflectedLocalSize (P i) (j i) e

lemma bracketProductBound_pos {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (j : ι→ℕ) : 0<bracketProductBound P j := by
  apply Finset.prod_pos
  intro i hi
  exact Finset.sum_pos (fun e _=>reflectedLocalSize_pos _ _ e) Finset.univ_nonempty

lemma bracketProduct_norm_le {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (j : ι→ℕ) (n b : O) :
    ‖∏i,bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3))‖≤
      bracketProductBound P j := by
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _=>norm_nonneg _)
  intro i hi
  rw [bracket_eq_sum_reflectedLocalPiece]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun e _=>reflectedLocalPiece_norm_le (P i) (hg i) (j i) e n b))

lemma completedCuspArrayWeight_ge_one (m : ℕ) (I J : NonzeroDualIdeal) :
    1≤completedCuspArrayWeight m I.val J.val := by
  have hi : 1≤Real.sqrt (Ideal.absNorm I.val:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (norm_at_least_one I.val I.property)
  rw [completedCuspArrayWeight_step]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ completedRamifiedStep_gt_one.le) hi)
    (norm_at_least_one J.val J.property)

lemma normalizedCuspCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : NonzeroDualIdeal) :
    ‖normalizedCuspCoefficient P hg j N c s b u m I.val J.val‖≤bracketProductBound P j := by
  have hw:=completedCuspArrayWeight_ge_one m I J
  have hw0 : 0≤completedCuspArrayWeight m I.val J.val:=zero_le_one.trans hw
  rw [normalizedCuspCoefficient,norm_div,norm_mul,norm_mul,ramifiedBracketPhase_norm,one_mul,
    Complex.norm_real,Real.norm_of_nonneg hw0]
  apply (div_le_div_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (completedCuspArray_norm N c s b u m I.val J.val)).trans
      (bracketProduct_norm_le P hg j _ _)) hw0).trans
  exact div_le_self (bracketProductBound_pos P j).le hw

/-- Absolute convergence permits the finite cusp and local-branch sums to be interchanged. -/
theorem normalizedCuspKernel_summable {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (V : ℝ→ℂ) (a b₀ : ℝ) (ha : 0<a) (hs : Function.support V⊆Set.Icc a b₀)
    (hV : ContDiff ℝ ∞ V) (scale : ℝ) (hscale : 0<scale) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspCoefficient P hg j N c s b u) x‖) :=
  rawDualKernelTerm_summable_norm V a b₀ ha hs hV scale 1 completedRamifiedStep
    (bracketProductBound P j) hscale zero_lt_one completedRamifiedStep_gt_one
    (bracketProductBound_pos P j).le _ (normalizedCuspCoefficient_norm P hg j N c s b u)

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff

lemma finite_first_summable_norm {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (hf : ∀a,Summable (fun b=>‖f a b‖)) :
    Summable (fun x : α×β=>‖f x.1 x.2‖) := by
  have hs : Summable (fun b=>∑a : α,‖f a b‖):=summable_sum (fun a _=>hf a)
  have hmajor:=((hasSum_fintype (fun _ : α=>(1:ℝ))).summable).mul_of_nonneg
    hs (fun _=>zero_le_one) (fun b=>Finset.sum_nonneg (fun a _=>norm_nonneg (f a b)))
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  simp only [one_mul]
  exact Finset.single_le_sum (fun a _=>norm_nonneg (f a x.2)) (Finset.mem_univ x.1)

theorem normalizedCuspFullKernel_summable {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (V : ℝ→ℂ) (a b₀ : ℝ) (ha : 0<a) (hs : Function.support V⊆Set.Icc a b₀)
    (hV : ContDiff ℝ ∞ V) (scale : ℝ) (hscale : 0<scale) :
    Summable (fun x : FullDualIdealIndex=>
      ‖rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspCoefficient P hg j N c s b x.1) x.2‖) := by
  letI : Finite Oˣ:=cubic_units_finite
  letI : Fintype Oˣ:=Fintype.ofFinite _
  apply finite_first_summable_norm
    (fun (u : Oˣ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal)=>
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspCoefficient P hg j N c s b u) x)
  intro u
  exact normalizedCuspKernel_summable P hg j N c s b u V a b₀ ha hs hV scale hscale

end CompletedGauss

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
