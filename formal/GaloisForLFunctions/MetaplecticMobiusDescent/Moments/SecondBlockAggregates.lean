/-
Second block aggregates adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondWindowBudgets

/-!
# Second block aggregates

Active sources and labels, source blocks, retained rows and the second retained and discarded
energies; squarefree and summed blocks from divisor envelopes and harmonic budgets.
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
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSourceSecondZeroEnergy
open Eisenstein HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => Eisenstein.O

def sourceSecondZero (S : Finset (Ideal O)) (β : Ideal O→ℂ) (η : Character) (t : ℝ) : ℂ :=
  secondZeroEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I => β I*heightCoeff η t I)

lemma heightCoeff_norm_le_one (η : Character) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact idealCoeff_norm_le_one η I

theorem secondZeroEnergy_filter {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (p : α→Prop) [DecidablePred p] (hc : ∀ i∈S,¬p i→c i=0) :
    secondZeroEnergy S a ha c=secondZeroEnergy (S.filter p) a ha c := by
  unfold secondZeroEnergy
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i
  · rw [if_pos hpi]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpj : p j
    · rw [if_pos hpj]
    · simp only [if_neg hpj,hc j hj hpj,star_zero,mul_zero,zero_mul]
  · simp only [if_neg hpi,hc i hi hpi,zero_mul,Finset.sum_const_zero]

lemma sourceGenerator_span (S : Finset (Ideal O)) (I : supportedColumns S) :
    Ideal.span {sourceGenerator S I}=(I:Ideal O) :=
  primary_span_supported I (Finset.mem_filter.mp I.property).2
lemma sourceGenerator_primary (S : Finset (Ideal O)) (I : supportedColumns S) :
    lambda^2∣sourceGenerator S I-1 :=
  (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I (Finset.mem_filter.mp I.property).2)).2
lemma sourceGenerator_injective (S : Finset (Ideal O)) : Function.Injective (sourceGenerator S) := by
  intro I J h
  apply Subtype.ext
  rw [←sourceGenerator_span S I,←sourceGenerator_span S J,h]

theorem sourceSecondZero_divisor_bound (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t B Y : ℝ) (hB : 0≤ B) (hY : 0≤ Y)
    (s : Ideal O) (hs : s≠0)
    (hc : ∀ I∈supportedColumns S,β I≠0→‖β I‖≤ B)
    (hdiv : ∀ I∈supportedColumns S,β I≠0→s∣I)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤ Y) :
    ‖sourceSecondZero S β η t‖≤128*B^2*Y/(Ideal.absNorm s:ℝ) := by
  let Q : Finset (supportedColumns S) := Finset.univ.filter (fun I => β I≠0)
  rw [sourceSecondZero,secondZeroEnergy_filter Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I => β I*heightCoeff η t I) (fun I => β I≠0)
      (by intro I _ h; simp only [not_not] at h; rw [h,zero_mul])]
  refine secondZeroEnergy_divisor_bound Q (sourceGenerator S) (sourceGenerator_supported S)
    (sourceGenerator_primary S) (sourceGenerator_injective S).injOn _ B hB ?_ s hs ?_ Y hY ?_
  · intro I hI
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heightCoeff_norm_le_one η t I
      (Finset.mem_filter.mp I.property).2.1) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hc I I.property (Finset.mem_filter.mp hI).2)
  · intro I hI
    rw [sourceGenerator_span]
    exact hdiv I I.property (Finset.mem_filter.mp hI).2
  · intro I hI
    rw [sourceGenerator_span]
    exact hN I I.property (Finset.mem_filter.mp hI).2

theorem sourceSecondZero_eq_zero_of_subunit (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t Y : ℝ) (hY : Y<1)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤ Y) :
    sourceSecondZero S β η t=0 := by
  have hc (I : supportedColumns S) : β I=0 := by
    by_contra hn
    have hi : (1:ℝ)≤ Ideal.absNorm (I:Ideal O) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp I.property).2.1)
    linarith [hN I I.property hn]
  simp only [sourceSecondZero,secondZeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B Y : ℝ),
      0≤ B → 1≤ Y → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤ B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤ Y) →
      ‖sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*B^2*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  let δ := ε/(2*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : δ*(N+2:ℕ)=ε/2 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi S β η t B Y hB hY hβ s hs hdiv hN
  let c := finiteColumnCoefficient S β
  have hY0 : 0< Y := zero_lt_one.trans_le hY
  have hbound (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      (Ideal.absNorm I:ℝ)≤ Y := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  have hbase : 1≤(1+D)*Y^δ := by
    have hp := Real.one_le_rpow hY hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      ‖c I‖≤ B*((1+D)^(N+2)*Y^(ε/2)) := by
    have hI0 := (Finset.mem_filter.mp hI).2.1
    have hdI : ((idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
      (hd I hI0).trans (mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hbound I hI hn) hδ.le) (by positivity) (by positivity))
    have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^(ε/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
    calc
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*Y^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := sourceSecondZero_divisor_bound (finiteColumns S) c η t
    (B*((1+D)^(N+2)*Y^(ε/2))) Y (by positivity) hY0.le s hs hcoeff
    (by
      intro I hI hn
      obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
      rw [←he]
      exact hdiv v hv hv0) hbound
  apply hb.trans_eq
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  calc
    _ = (128*((1+D)^(N+2))^2)*B^2*((Y^(ε/2))^2*Y)/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [hp]

theorem normalized_tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B L T : ℝ),
      0≤ B → 0< L → 0< T → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤ B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤ L*T) →
      (L*T<1 → sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0) ∧
      ∀ κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*‖κ‖*B^2*L^(1+ε)*T^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi S β η t B L T hB hL hT hβ s hs hdiv hN
  have hz (hsmall : L*T<1) : sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0 := by
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*T) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  refine ⟨hz,?_⟩
  intro κ
  by_cases hsmall : L*T<1
  · rw [hz hsmall,mul_zero,norm_zero]
    positivity
  have hb := hbound hi S β η t B (L*T) hB (le_of_not_gt hsmall) hβ s hs hdiv hN
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hT.le)).trans_eq
  rw [Real.mul_rpow hL.le hT.le,Real.rpow_add hT,Real.rpow_one]
  field_simp

lemma profileCoefficient_dvd {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    s∣finiteTupleProduct v := by
  by_contra h
  exact hv (by simp only [profileCoefficient,if_neg h,mul_zero])

theorem profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P D b : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (D₁ D₂ b₁ b₂ : ℝ),
      (∀ j,0≤ D j) → 0≤ D₁ → 0≤ D₂ → (∀ j,0≤ b j) → 0≤ b₁ → 0≤ b₂ →
      (∀ j x,‖Wslot j x‖≤ D j) → (∀ x,‖W₁ x‖≤ D₁) → (∀ x,‖W₂ x‖≤ D₂) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤ b j) → (∀ x,W₁ x≠0→x≤ b₁) → (∀ x,W₂ x≠0→x≤ b₂) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let L := (∏ j,b j)*b₁*b₂
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (L*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤ C*‖κ‖*(2*D₁*D₂*(∏ j,D j))^2*(1+L)^(1+ε)*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P D b W₁ W₂ D₁ D₂ b₁ b₂
    hD hD₁ hD₂ hb hb₁ hb₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw L E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤2*D₁*D₂*(∏ j,D j) :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂
      hslot h₁ h₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hn₁ : (0:ℝ)< Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)< Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hraw : 0< Traw := mul_pos (div_pos hT (mul_pos hn₁ hn₂)) (Finset.prod_pos (fun j _=> hP j))
  have hL : 0≤ L := mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=> hb j)) hb₁) hb₂
  have hN (v : Tuple ι) (hv : β v≠0) : (Ideal.absNorm (finiteTupleProduct v):ℝ)≤ L*Traw := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hs₁ hs₂ v hv
    exact hh.2.trans_eq (by dsimp only [L,Traw];ring)
  refine ⟨?_,?_⟩
  · intro hsmall
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*Traw) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv0
  · exact (hbound hi S β η t (2*D₁*D₂*(∏ j,D j)) (1+L) Traw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD₁) hD₂) (Finset.prod_nonneg (fun j _=> hD j)))
      (by linarith) hraw (fun v _ _=> hβ v) s hsz
      (fun v _ hv=> profileCoefficient_dvd R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hv)
      (fun v _ hv=>(hN v hv).trans (mul_le_mul_of_nonneg_right (by linarith : L≤1+L) hraw.le))).2

theorem bounded_profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε)
    (D b : ℝ) (hD : 0≤ D) (hb : 0≤ b) :
    ∃ C : ℝ,0< C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤ N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ),
      (∀ j x,‖Wslot j x‖≤ D) → (∀ x,‖W₁ x‖≤ D) → (∀ x,‖W₂ x‖≤ D) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤ b) → (∀ x,W₁ x≠0→x≤ b) → (∀ x,W₂ x≠0→x≤ b) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (b^(Fintype.card ι+2)*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤ C*‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C₀,hC₀,hmain⟩ := profile_second_zero_energy N ε hε
  let B := 2*D*D*(1+D)^N
  let L := (1+b)^(N+2)
  let C := C₀*(1+B^2)*(1+L)^(1+ε)
  have hB : 0≤ B := by dsimp [B];positivity
  have hL : 0≤ L := by dsimp [L];positivity
  have hC : 0< C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P W₁ W₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw E
  have hTpos : 0< T := hX ▸ mul_pos hX₁ hX₂
  have hraw0 : 0≤ Traw := mul_nonneg (div_nonneg hTpos.le (by positivity))
    (Finset.prod_nonneg (fun j _=>(hP j).le))
  have hh := hmain hi η t R ν hν Wslot P (fun _=> D) (fun _=> b) W₁ W₂ D D b b
    (fun _=> hD) hD hD (fun _=> hb) hb hb hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  simp only [Finset.prod_const,Finset.card_univ] at hh
  have heL : b^Fintype.card ι*b*b=b^(Fintype.card ι+2) := by
    rw [pow_add,pow_two];ring
  rw [heL] at hh
  refine ⟨hh.1,?_⟩
  intro κ
  have hBbound : 2*D*D*D^Fintype.card ι≤ B := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_left₀ hD (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  have hLbound : b^(Fintype.card ι+2)≤ L :=
    (pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hpow : (1+b^(Fintype.card ι+2))^(1+ε)≤(1+L)^(1+ε) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hcoef : C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε)≤ C := by
    dsimp only [C]
    apply mul_le_mul _ hpow (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    exact (pow_le_pow_left₀ (by positivity) hBbound 2).trans (by linarith)
  apply (hh.2 κ).trans
  calc
    _ = (C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε))*
        (‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) := by ring
    _ ≤ C*(‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

theorem smooth_subset_source_second_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α→ℝ→ℂ) (W₁ W₂ : ℝ→ℂ) (a b : α→ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0< a j) (hb : ∀ j∈F,0≤ b j)
    (ha₁ : 0< a₁) (hb₁ : 0≤ b₁) (ha₂ : 0< a₂) (hb₂ : 0≤ b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : α→Ideal O→ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) → ∀ (P : α→ℝ)
      (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0< P j) → 0< X₁ → 0< X₂ → 0< Y₁ → 0< Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T →
      ∀ (pools : (J⊕Fin 2)→Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),
      let S := Fintype.piFinset pools
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let Y := (∏ j∈J,b j)*b₁*b₂*Traw
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=> Wslot j.val) (fun j : J=> P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (Y<1 → E=0) ∧
        ‖(((K:ℂ)*SchwartzPlanePoisson.paperRadialFourier Φ 0)/(Traw:ℂ))*E‖≤
          C*‖(K:ℂ)*SchwartzPlanePoisson.paperRadialFourier Φ 0‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  choose D hD hDb hz hsb using fun j : F => smooth_annular_bound
    (Wslot j.val) (a j.val) (b j.val) (ha j.val j.property)
    (hsSlot j.val j.property) (hWslot j.val j.property)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let Dmax := 1+D₁+D₂+∑ j : F,D j
  let bmax := 1+b₁+b₂+∑ j : F,b j.val
  have hDs : 0≤∑ j : F,D j := Finset.sum_nonneg (fun j _=> hD j)
  have hbs : 0≤∑ j : F,b j.val := Finset.sum_nonneg (fun j _=> hb j.val j.property)
  have hDmax : 0≤ Dmax := by dsimp only [Dmax];linarith
  have hbmax : 0≤ bmax := by dsimp only [bmax];linarith
  have hD₁max : D₁≤ Dmax := by dsimp only [Dmax];linarith
  have hD₂max : D₂≤ Dmax := by dsimp only [Dmax];linarith
  have hb₁max : b₁≤ bmax := by dsimp only [bmax];linarith
  have hb₂max : b₂≤ bmax := by dsimp only [bmax];linarith
  have hDj (j : F) : D j≤ Dmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=> hD k) (Finset.mem_univ j)
    dsimp only [Dmax]
    linarith
  have hbj (j : F) : b j.val≤ bmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=> hb k.val k.property) (Finset.mem_univ j)
    dsimp only [bmax]
    linarith
  obtain ⟨C,hC,hbound⟩ := bounded_profile_second_zero_energy F.card ε hε Dmax bmax hDmax hbmax
  refine ⟨C,hC,?_⟩
  intro J hJ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY pools Φ K S Traw Y E
  let β := profileCoefficient R (fun j : J=>ν j.val) (fun j : J=> Wslot j.val) (fun j : J=> P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hcard : Fintype.card J≤ F.card := by simpa only [Fintype.card_coe] using Finset.card_le_card hJ
  have hh := hbound hcard η t R (fun j : J=>ν j.val) (fun j I=> hν j.val j.property I)
    (fun j : J=> Wslot j.val) (fun j : J=> P j.val) W₁ W₂
    (fun j x=>(hDb ⟨j.val,hJ j.property⟩ x).trans (hDj ⟨j.val,hJ j.property⟩))
    (fun x=>(hDb₁ x).trans hD₁max) (fun x=>(hDb₂ x).trans hD₂max)
    (fun j=> hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j x hx=>(hsb ⟨j.val,hJ j.property⟩ x hx).trans (hbj ⟨j.val,hJ j.property⟩))
    (fun x hx=>(hsb₁ x hx).trans hb₁max) (fun x hx=>(hsb₂ x hx).trans hb₂max)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=> hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  rw [Finset.prod_coe_sort] at hh
  refine ⟨?_,hh.2 ((K:ℂ)*SchwartzPlanePoisson.paperRadialFourier Φ 0)⟩
  intro hsmall
  apply sourceSecondZero_eq_zero_of_subunit _ _ η t Y hsmall
  intro I hI hn
  obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
  have hN := profileCoefficient_product_bound R (fun j : J=>ν j.val)
    (fun j : J=> Wslot j.val) (fun j : J=> P j.val) (fun j : J=> b j.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=> hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (fun j=> hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j=> hsb ⟨j.val,hJ j.property⟩) hsb₁ hsb₂ v hv0
  rw [←he]
  exact hN.2.trans_eq (by rw [Finset.prod_coe_sort,Finset.prod_coe_sort];dsimp only [Y,Traw];ring)

end CenteredMomentSourceSecondZeroEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondTail
open Eisenstein  SchwartzPlanePoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => Eisenstein.O

theorem actual_second_kernel_reference (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (K X H Tsec : ℝ) (hK : 0< K) (hX : 0< X)
    (hi : (Ideal.absNorm I:ℝ)≤ Real.exp H*X) (hj : (Ideal.absNorm J:ℝ)≤ Real.exp H*X)
    (hsec : X^2/K≤ Tsec) :
    kernelReference Tsec H≤ K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hT : 0< Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hNi := CenteredMomentFirstScale.norm_pos I hI
  have hNj := CenteredMomentFirstScale.norm_pos J hJ
  have hprod : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤ Real.exp (2*H)*X^2 := by
    apply (mul_le_mul hi hj hNj.le (by positivity)).trans_eq
    rw [show 2*H=H+H by ring,Real.exp_add]
    ring
  unfold kernelReference
  apply (le_div_iff₀ (mul_pos hNi hNj)).mpr
  calc
    _ ≤ (Real.exp (-2*H)/Tsec)*(Real.exp (2*H)*X^2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = X^2/Tsec := by
      rw [show -2*H=-(2*H) by ring,Real.exp_neg]
      field_simp
    _ ≤ K := (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hsec)

def secondDiscardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryIdealGenerator I) (primaryIdealGenerator J)
        ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖ringComplex h‖^2/
        ‖ringComplex (primaryIdealGenerator I*primaryIdealGenerator J)‖^2)

theorem second_discarded_pair_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0< C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
        (K X H Tsec Z Csec ξ : ℝ),0< K → 0< X → 1< Z → 1≤ Csec →
      (Ideal.absNorm I:ℝ)≤ Real.exp H*X → (Ideal.absNorm J:ℝ)≤ Real.exp H*X →
      X^2/K≤ Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedPair I J hI hJ W K Tsec Z ξ‖≤
        K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_second_tail Adec
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ K X H Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hT : 0< Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hb := ht W Tsec Z Csec H ξ (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))
    hT hZ hCs hthreshold (actual_second_kernel_reference I J hI.1 hJ.1 K X H Tsec hK hX hi hj hsec)
    (primaryIdealGenerator I) (primaryIdealGenerator J)
    ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ)
  have he (h : O) : K*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator I*primaryIdealGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  have hu : normValue (primaryIdealGenerator I)=(Ideal.absNorm I:ℝ) := by rw [normValue,primary_span_supported I hI]
  have hv : normValue (primaryIdealGenerator J)=(Ideal.absNorm J:ℝ) := by rw [normValue,primary_span_supported J hJ]
  rw [hu,hv] at hb
  have hNi : (1:ℝ)≤ Ideal.absNorm I := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hNj : (1:ℝ)≤ Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hroot : 1≤ Real.sqrt (Ideal.absNorm I:ℝ)*Real.sqrt (Ideal.absNorm J:ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hNi) (Real.one_le_sqrt.mpr hNj)
  have hnorm : ‖(K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))‖≤ K := by
    rw [norm_div,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hK.le hroot
  unfold secondDiscardedPair
  simp_rw [he]
  rw [norm_mul]
  apply (mul_le_mul hnorm hb (norm_nonneg _) hK.le).trans
  have hprod := mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity : 0≤ Real.exp H*X)
  have hfac : 0≤(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hfac) hK.le
  convert hb' using 1 <;> first | rfl | ring

end CenteredMomentSecondTail

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSupportedTailAggregate
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondTail CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => Eisenstein.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤ B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤ B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

def secondDiscardedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem second_discarded_energy_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0< C ∧
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0< K → 0< X → 1< Z → 1≤ Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤ Real.exp H*X) →
      X^2/K≤ Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := second_discarded_pair_bound Adec
  refine ⟨s,C,hC,?_⟩
  intro η t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤ B := by dsimp only [B];positivity
  have hweight (I : supportedColumns S) : ‖heightCoeff η t I‖≤1 := by
    rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp I.property).2]
    exact rowWeight_norm_le_one η fixedBadMask 1 1 t I (Finset.mem_filter.mp I.property).2.1
  have hp := pair_mass (fun I : supportedColumns S => c I) (fun I => heightCoeff η t I)
    (fun I J => secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ) hweight B hB
    (fun I J hi hj => ht W I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 K X H Tsec Z Csec ξ hK hX hZ hCs
      (hN I (Finset.mem_filter.mp I.property).1 hi) (hN J (Finset.mem_filter.mp J.property).1 hj) hsec hthreshold)
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 <;> first | rfl | (dsimp only [B];ring)

theorem first_discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0< C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0< K → 0< X → 1< Z → 1≤ Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤ Real.exp H*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,c I≠0 → c J≠0 →
        ∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤ Tsec) →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤ B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤ B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj (hsec I J hi hj) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ)
    (fun I => rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 <;> first | rfl | (dsimp only [B];ring)

end CenteredMomentSupportedTailAggregate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CompletedGauss  SchwartzPlanePoisson
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSourcePoisson CenteredMomentSecondWholeKernel CenteredMomentSecondTail
open CenteredMomentFirstLocalization CenteredMomentSectorLocalization CenteredMomentSupportedCorrelation
open CenteredMomentSupportedTailAggregate CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal
local notation "O" => Eisenstein.O

def secondRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryIdealGenerator I) (primaryIdealGenerator J)
        ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖ringComplex h‖^2/
        ‖ringComplex (primaryIdealGenerator I*primaryIdealGenerator J)‖^2)

theorem secondSourceKernel_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        actualCorrelation (primaryIdealGenerator I) (primaryIdealGenerator J)
          ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ) 0*
          paperRadialFourier W 0+
      secondRetainedPair I J hI hJ W K Tsec Z ξ+
      secondDiscardedPair I J hI hJ W K Tsec Z ξ := by
  have hpI := (supported_span_primaryIdealGenerator_iff I).mpr hI
  have hpJ := (supported_span_primaryIdealGenerator_iff J).mpr hJ
  have hk : 0< K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos I hI.1) (CenteredMomentFirstScale.norm_pos J hJ.1))
  have hs := lattice_fourier_split W _ hk
    (fun h => actualCorrelation (primaryIdealGenerator I) (primaryIdealGenerator J) hpI hpJ (-h))
    _ (fun h => CenteredMomentTail.actualCorrelation_norm_le _ _ hpI hpJ (-h))
    (frequencyRadius Tsec Z ξ)
  have he (h : O) : K*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator I*primaryIdealGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  rw [secondSourceKernel_poisson I J hI hJ W K hK]
  unfold secondRetainedPair secondDiscardedPair
  simp_rw [he]
  rw [hs]
  simp only [neg_zero]
  ring

def secondRetainedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem sourceGaussEnergy_localized (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff η t) W K=
      ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β η t+
      secondRetainedEnergy η t S β W K Tsec Z ξ+
      secondDiscardedEnergy η t S β W K Tsec Z ξ := by
  rw [sourceGaussEnergy_poisson η t S β W K hK]
  unfold sourceSecondZero secondZeroEnergy secondRetainedEnergy secondDiscardedEnergy
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  have he := secondSourceKernel_split I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ hK
  rw [secondSourceKernel_poisson I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K hK] at he
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  convert congrArg (fun x : ℂ => ((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*x) he using 1 <;> ring

end CenteredMomentSecondLocalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentActiveSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
local notation "O" => Eisenstein.O

def activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) : Finset (Ideal O) :=
  S.filter (fun I => β I≠0)

@[simp] theorem mem_activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) (I : Ideal O) :
    I∈activeSource S β ↔ I∈S ∧ β I≠0 := Finset.mem_filter

theorem supportedColumns_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    supportedColumns (activeSource S β)=(supportedColumns S).filter (fun I => β I≠0) := by
  ext I
  simp only [supportedColumns,activeSource,Finset.mem_filter]
  tauto

theorem active_sum (S : Finset (Ideal O)) (β F : Ideal O → ℂ) :
    (∑I∈supportedColumns (activeSource S β),β I*F I)=
      ∑I∈supportedColumns S,β I*F I := by
  rw [supportedColumns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with h <;> simp_all

theorem sourceGaussEnergy_active (S : Finset (Ideal O)) (β f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (activeSource S β) β f W K=sourceGaussEnergy S β f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro z
  congr 2
  have hp := source_gaussPolynomial (activeSource S β) (fun I => β I*f I) z
  have hq := source_gaussPolynomial S (fun I => β I*f I) z
  rw [hp,hq]
  congr 2
  simpa only [mul_assoc] using active_sum S β (fun I => f I*primaryGaussRow I z)

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    secondRetainedPair I J hI hJ W K T Z ξ else 0 else 0

theorem secondRetainedEnergy_eq_sum (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K T Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*CenteredMomentHeckeColumnWindow.heightCoeff η t I)*
          star (β J*CenteredMomentHeckeColumnWindow.heightCoeff η t J))*
          retainedKernel I J W K T Z ξ := by
  unfold secondRetainedEnergy
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel,dif_pos (Finset.mem_filter.mp I.property).2,
    dif_pos (Finset.mem_filter.mp J.property).2]

theorem secondRetainedEnergy_active (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t (activeSource S β) β W K T Z ξ=
      secondRetainedEnergy η t S β W K T Z ξ := by
  rw [secondRetainedEnergy_eq_sum,secondRetainedEnergy_eq_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β I=0
  · simp [hi]
  · rw [if_pos hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : β J=0 <;> simp [hj]

theorem commonLabel_witnesses (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    ∃I∈S,∃J∈S,Supported I ∧ Supported J ∧ β I≠0 ∧ β J≠0 ∧
      commonPart I J=C ∧ commonPart J I=D := by
  obtain ⟨⟨I,J⟩,hp,he⟩ := Finset.mem_image.mp h
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  obtain ⟨hi,hIs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hJs⟩ := Finset.mem_filter.mp hj
  obtain ⟨hi,hβi⟩ := mem_activeSource S β I |>.mp hi
  obtain ⟨hj,hβj⟩ := mem_activeSource S β J |>.mp hj
  exact ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

theorem commonLabel_norm_bounds (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H)
    (C D : Ideal O) (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    (Ideal.absNorm C:ℝ)≤ H ∧ (Ideal.absNorm D:ℝ)≤ H := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β C D h
  constructor
  · rw [←hC]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le I J hIs.1)).trans (hH I hi hβi)
  · rw [←hD]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le J I hJs.1)).trans (hH J hj hβj)

theorem residualPool_data (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H)
    (C : Ideal O) (hC : C≠0) (a : Ideal O)
    (ha : a∈residualPool C hC (supportedColumns (activeSource S β))) :
    C*a∈S ∧ β (C*a)≠0 ∧ Supported (C*a) ∧ a≠0 ∧
      1≤(Ideal.absNorm a:ℝ) ∧ (Ideal.absNorm a:ℝ)≤ H/(Ideal.absNorm C:ℝ) := by
  have hm := (mem_residualPool C hC _ a).mp ha
  obtain ⟨hm,hsa⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm,hβ⟩ := (mem_activeSource S β (C*a)).mp hm
  have ha0 : a≠0 := right_ne_zero_of_mul hsa.1
  have hpos := CenteredMomentFirstScale.norm_pos C hC
  have hab := hH (C*a) hm hβ
  rw [map_mul,Nat.cast_mul] at hab
  refine ⟨hm,hβ,hsa,ha0,?_,?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha0)
  · exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hab)

theorem source_energy_active_sectors (τ : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    sourceGaussEnergy S β (CenteredMomentHeckeColumnWindow.heightCoeff τ t) W K =
      ∑p∈commonLabels (supportedColumns (activeSource S β))
        (supportedColumns (activeSource S β)),
      ∑q∈pairSector p.1 p.2 (supportedColumns (activeSource S β))
        (supportedColumns (activeSource S β)),
      ((β q.1*CenteredMomentHeckeColumnWindow.heightCoeff τ t q.1)*
        star (β q.2*CenteredMomentHeckeColumnWindow.heightCoeff τ t q.2))*
        CenteredMomentSecondSourceEnergy.secondSourceKernel q.1 q.2 W K := by
  rw [←sourceGaussEnergy_active S β]
  exact CenteredMomentSecondSourceEnergy.source_energy_common_sectors τ t _ β W K hK

end CenteredMomentActiveSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondRetainedPair
open CanonicalQuadraticSieve CompletedGauss  SchwartzPlanePoisson
open CenteredMomentSecondSectorRetained CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSecondLocalization CenteredMomentSourceRow
local notation "O" => Eisenstein.O

theorem physical_pair_summable (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K) :
    Summable (fun j : O=> idealCorrelation (C*I) (D*J) hI hJ j*physicalKernel C D W K R j I J) := by
  have hk : 0< K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hI.1) (CenteredMomentFirstScale.norm_pos _ hJ.1))
  have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hI hJ j‖≤
      (Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J) := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
      ((supported_span_primaryIdealGenerator_iff _).mpr hI) ((supported_span_primaryIdealGenerator_iff _).mpr hJ) j
    simpa only [idealCorrelation,primary_span_supported _ hI,primary_span_supported _ hJ] using hh
  have hs := weighted_fourier_summable W _ hk (fun j=> idealCorrelation (C*I) (D*J) hI hJ j)
    (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=> retained_complex_norm R _)
  have he (j : O) : K*‖ringComplex j‖^2/‖ringComplex (primaryIdealGenerator (C*I)*primaryIdealGenerator (D*J))‖^2=
      (K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)))*normValue j := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hI,primary_norm_sq _ hJ,normValue_eq_embedding]
    ring
  convert hs.mul_left
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ))) using 1
  all_goals try rfl
  funext j
  dsimp only [physicalKernel]
  rw [he]
  ring

theorem retainedPair_positive_frequency (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedPair I J hI hJ W K Tsec Z ξ=
      ∑' j : O,idealCorrelation I J hI hJ j*physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J := by
  have he := (Equiv.neg O).tsum_eq (fun j : O=> idealCorrelation I J hI hJ j*
    physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J)
  simp only [Equiv.neg_apply,physicalKernel,one_mul,map_neg,norm_neg,
    normValue_eq_embedding] at he
  simp only [physicalKernel,one_mul,normValue_eq_embedding]
  rw [←he]
  unfold secondRetainedPair
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [idealCorrelation,normValue_eq_embedding]
  ring

end CenteredMomentSecondRetainedPair

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondSourceRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondLocalization CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained CenteredMomentSecondRetainedPair
open CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then secondRetainedPair I J hI hJ W K Tsec Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel I J W K Tsec Z ξ=secondRetainedPair I J hI hJ W K Tsec Z ξ := by
  simp only [retainedKernel,dif_pos hI,dif_pos hJ]

theorem retainedEnergy_common_sectors (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
            retainedKernel q.1 q.2 W K Tsec Z ξ := by
  let F := fun I J : Ideal O=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
    retainedKernel I J W K Tsec Z ξ
  have he : secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      retainedKernel (C*I) (D*J) W K Tsec Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
      retainedKernel I J W K Tsec Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

theorem retainedKernel_physical (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel (C*I) (D*J) W K Tsec Z ξ=
      ∑' j : O,idealCorrelation (C*I) (D*J) hI hJ j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J := by
  rw [retainedKernel_eq _ _ hI hJ,retainedPair_positive_frequency]
  simp only [physicalKernel,one_mul]

end CenteredMomentSecondSourceRetained

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondSourceFrequency
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondSourceRetained CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained
open CenteredMomentSecondRetainedPair CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => Eisenstein.O

theorem retained_sector_eq_physical (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑' j : O,sectorFrequency η t S β C D hC hD
          (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j := by
  rw [retained_sector_independent η t S β C D hC.1 hD.1 hCD]
  congr 1
  let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
  let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
  have hci (I : sectorPool C hC.1 S) : Supported (C*(I:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
  have hdj (J : sectorPool D hD.1 S) : Supported (D*(J:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
  let f := fun (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) (j : O)=>
    if IsCoprime (I:Ideal O) (J:Ideal O) then
      (c I*star (d J))*(idealCorrelation (C*I) (D*J) (hci I) (hdj J) j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J) else 0
  have hs (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) : Summable (f I J) := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simpa only [f,if_pos hc] using (physical_pair_summable C D I J (hci I) (hdj J)
        W K (frequencyRadius Tsec Z ξ) hK).mul_left (c I*star (d J))
    · simp only [f,if_neg hc];exact summable_zero
  have hp (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
          retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0)=∑' j : O,f I J j := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simp only [f,if_pos hc]
      rw [retainedKernel_physical C D I J (hci I) (hdj J),tsum_mul_left]
    · simp only [f,if_neg hc,tsum_zero]
  have hf (j : O) : sectorFrequency η t S β C D hC hD
      (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j=
      ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,f I J j := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f,c,d]
    split_ifs <;> ring
  simp_rw [hp]
  rw [tsum_congr hf, Summable.tsum_finsetSum (fun I _=> summable_sum (fun J _=> hs I J))]
  exact Finset.sum_congr rfl (fun I _=>(Summable.tsum_finsetSum (fun J _=> hs I J)).symm)

theorem original_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ U : Finset (CommonIndex C D),∑' h : O,
          if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
            sectorFrequency η t S β C D hC hD
              (physicalKernel C D W K (frequencyRadius Tsec Z ξ))
              ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [retained_sector_eq_physical η t S β C D hC hD hCD W K Tsec Z ξ hK,
    actual_retained_sector_GV η t S β C D hC hD hCD W K (frequencyRadius Tsec Z ξ) hK]

end CenteredMomentSecondSourceFrequency

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondRetainedAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSourceRetained CenteredMomentSecondSourceFrequency
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon
local notation "O" => Eisenstein.O

theorem commonLabels_supported (S : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported C ∧ Supported D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact ⟨commonPart_supported _ _ (Finset.mem_filter.mp hp'.1).2,
    commonPart_supported _ _ (Finset.mem_filter.mp hp'.2).2⟩

theorem original_retained_energy_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0< K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  exact original_retained_sector_GV η t S β p.val.1 p.val.2
    (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2
    (commonLabels_data _ _ _ _ p.property).2.2 W K Tsec Z ξ hK

end CenteredMomentSecondRetainedAggregate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondRetainedRows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss 
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => Eisenstein.O

def retainedRows (R : ℝ) (A : O) : Finset O := TruncatedPrincipalPoisson.rowNormDisk (Nat.ceil (4*R/normValue A))

theorem retained_mem_rows (R : ℝ) (A h : O) (hA : A≠0)
    (hh : retainedWeight R (normValue (A*h))≠0) : h∈retainedRows R A := by
  have he := retainedWeight_enclosure R _ hh
  have hAh : A*h≠0 := by
    intro hz
    have hn : normValue (A*h)=0 := by simp [hz,normValue]
    linarith [he.1]
  have hh0 : h≠0 := right_ne_zero_of_mul hAh
  apply (TruncatedPrincipalPoisson.mem_rowNormDisk _ _).mpr
  constructor
  · have hn := normValue_pos h hh0
    unfold normValue at hn
    exact_mod_cast hn
  · have hbound : normValue h≤4*R/normValue A := by
      apply (le_div_iff₀ (normValue_pos A hA)).mpr
      simpa only [normValue_mul,mul_comm] using he.2
    have hb := hbound.trans (Nat.le_ceil (4*R/normValue A))
    unfold normValue at hb
    exact_mod_cast hb

theorem physical_sector_zero_of_weight (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (j : O)
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem physical_partition_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A : O) (hA : A≠0) (part : O→Prop) :
    (∑' h : O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  intro h hh
  by_cases hp : part h
  · rw [if_pos hp]
    apply physical_sector_zero_of_weight η t S β C D hC hD W K R (A*h)
    by_contra hn
    exact hh (retained_mem_rows R A h hA hn)
  · rw [if_neg hp]

theorem actual_GV_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _

end CenteredMomentSecondRetainedRows

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondDyadicPartition
open HeckeFamily CanonicalQuadraticSieve  SchwartzPlanePoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic CenteredMomentDyadicCount
local notation "O" => Eisenstein.O

abbrev Blocks (a b : Fin 4→ℝ) := ∀ i : Fin 4,↥(indices (a i) (b i))

theorem dyadic_product_partition (a b q : Fin 4→ℝ)
    (ha : ∀i,0< a i) (hq : ∀i,q i∈Set.Icc (a i) (b i)) :
    (∑ n : Blocks a b,∏ i : Fin 4,dyadicWeight (n i) (q i))=1 := by
  change (∑ n : (∀ i : Fin 4,↥(indices (a i) (b i))),∏ i : Fin 4,dyadicWeight (n i) (q i))=1
  rw [←Fintype.prod_sum (fun (i : Fin 4) (n : indices (a i) (b i))=> dyadicWeight n (q i))]
  have he (i : Fin 4) : (∑ n : indices (a i) (b i),dyadicWeight n (q i))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun n : ℤ=> dyadicWeight n (q i))]
    exact dyadic_partition_on_interval _ _ _ (ha i) (hq i)
  simp_rw [he]
  simp

theorem physical_kernel_dyadic_partition (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K)
    (a b : Fin 4→ℝ) (ha : ∀i,0< a i)
    (hband : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)] : Fin 4→ℝ) i∈Set.Icc (a i) (b i)) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks a b,
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
          (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
          (retainedWeight R (normValue (A*h)):ℂ)*
            wholeKernel W (fun _=> logAnnulus)
              (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
              (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
              (Real.log (normValue h/dyadicScale (n 1)))
              (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
              (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  let q : Fin 4→ℝ := ![secondEffectiveScale C D A K,normValue h,
    (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)]
  have he : (∑ n : Blocks a b,((∏i : Fin 4,dyadicWeight (n i) (q i)):ℝ):ℝ)=1 :=
    dyadic_product_partition a b q ha hband
  calc
    _ = physicalKernel C D W K R (A*h) I J*(1:ℂ) := (mul_one _).symm
    _ = ∑ n : Blocks a b,physicalKernel C D W K R (A*h) I J*
        ((∏i : Fin 4,dyadicWeight (n i) (q i):ℝ):ℂ) := by
      rw [←Finset.mul_sum,←Complex.ofReal_sum,he,Complex.ofReal_one]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Fin.prod_univ_four]
      exact physical_kernel_dyadic C D I J hC hD hI hJ A h hA hh W K R hK (fun i=> n i)

end CenteredMomentSecondDyadicPartition

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => Eisenstein.O

def sourceLower (C D : Ideal O) (A : O) (K : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,1,1,1]

def sourceUpper (C D : Ideal O) (A : O) (K R H : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,max 1 (4*R/normValue A),
    max 1 (H/(Ideal.absNorm C:ℝ)),max 1 (H/(Ideal.absNorm D:ℝ))]

def dyadicKernel (C D : Ideal O) (A : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (n : Fin 4→ℤ) (h : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
    (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
    (retainedWeight R (normValue (A*h)):ℂ)*
      wholeKernel W (fun _=> logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue h/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))

theorem active_sector_norm (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H)
    (C : Ideal O) (hC : C≠0) (I : sectorPool C hC (activeSource S β)) :
    (Ideal.absNorm (I:Ideal O):ℝ)∈Set.Icc 1 (max 1 (H/(Ideal.absNorm C:ℝ))) := by
  have hh := residualPool_data S β H hH C hC I (Finset.mem_filter.mp I.property).1
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.trans (le_max_right _ _)⟩

theorem sourceLower_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0< K) : ∀i,0< sourceLower C D A K i := by
  intro i
  fin_cases i
  · exact secondEffectiveScale_pos C D hC hD A hA K hK
  all_goals norm_num [sourceLower]

theorem active_physical_kernel_partition (_η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        dyadicKernel C D A W K R (fun i=> n i) h I J := by
  by_cases hw : retainedWeight R (normValue (A*h))=0
  · simp only [physicalKernel,dyadicKernel,hw,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  have he := retainedWeight_enclosure R _ hw
  have hh : h≠0 := by
    intro hz
    subst h
    simp [normValue] at he
  have hrow : normValue h≤4*R/normValue A := by
    apply (le_div_iff₀ (normValue_pos A hA)).mpr
    simpa only [normValue_mul,mul_comm] using he.2
  have hb : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm (I:Ideal O):ℝ),(Ideal.absNorm (J:Ideal O):ℝ)] : Fin 4→ℝ) i∈
        Set.Icc (sourceLower C D A K i) (sourceUpper C D A K R H i) := by
    intro i
    fin_cases i
    · exact ⟨le_rfl,le_rfl⟩
    · exact ⟨normValue_ge_one h hh,hrow.trans (le_max_right _ _)⟩
    · exact active_sector_norm S β H hH C hC.1 I
    · exact active_sector_norm S β H hH D hD.1 J
  exact physical_kernel_dyadic_partition C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK _ _ (sourceLower_pos C D hC.1 hD.1 A hA K hK) hb

end CenteredMomentSecondActiveDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondBlockAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss 
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSectorFrequency
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
local notation "O" => Eisenstein.O

abbrev ActiveLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  ↥(commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)))

abbrev SourceBlocks (C D : Ideal O) (U : Finset (CommonIndex C D)) (K R H : ℝ) :=
  Blocks (sourceLower C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)
    (sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H)

lemma retainedRows_ne_zero (R : ℝ) (A z : O) (hz : z∈retainedRows R A) : z≠0 := by
  have hp := ((TruncatedPrincipalPoisson.mem_rowNormDisk _ _).mp hz).1
  intro h
  simp [h] at hp

theorem active_kernel_windows (η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        physicalKernel C D W K R (A*h) I J*
          ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
            dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
            dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ) := by
  refine (active_physical_kernel_partition η S β H hH C D hC hD I J A h hA W K R hK).trans ?_
  apply Finset.sum_congr rfl
  intro n hn
  exact (physical_kernel_dyadic C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK (fun i=> n i)).symm

theorem sector_finite_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0< K) :
    let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t (activeSource S β) β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑n : SourceBlocks C D U K R H,
        physicalBlock η t (activeSource S β) β C D hC hD U R (retainedRows R A) W K
          (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*h)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [active_kernel_windows η S β H hH C D hC hD I J _ h hA
      (retainedRows_ne_zero R _ h hh) W K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

theorem original_secondRetainedEnergy_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0< K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p : ActiveLabel S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (retainedRows (frequencyRadius Tsec Z ξ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              W K (fun i=>(n i:ℤ)) := by
  rw [←secondRetainedEnergy_active η t S β W K Tsec Z ξ,
    original_retained_energy_GV η t (activeSource S β) β W K Tsec Z ξ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact sector_finite_blocks η t S β H hH _ _ _ _ U W K _ hK

lemma common_height_norm_le_one (η : Character) (t : ℝ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) :
    ‖heightCoeff η t C*star (heightCoeff η t D)‖≤1 := by
  rw [norm_mul,norm_star]
  have hc := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t C hC
  have hd := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t D hD
  nlinarith [norm_nonneg (heightCoeff η t C),norm_nonneg (heightCoeff η t D)]

theorem original_secondRetainedEnergy_norm_le (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0< K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H) :
    ‖secondRetainedEnergy η t S β W K Tsec Z ξ‖≤
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
            W K (fun i=>(n i:ℤ))‖ := by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end CenteredMomentSecondBlockAggregate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => Eisenstein.O

def liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ):Finset (ActiveLabel S β):=
  Finset.univ.filter (fun p=> idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0)

lemma mem_liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β):
    p∈liveLabels η S β ↔ idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0:=by
  simp only [liveLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma common_height_zero_of_not_live (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:idealCoeff η p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

theorem original_live_blocks (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H:ℝ) (hK:0< K)
    (hH:∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (liveRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)
                (retainedRows (frequencyRadius Tsec Z ξ)
                  (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)))
              W K (fun i=>(n i:ℤ)):=by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  trans ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
          W K (fun i=>(n i:ℤ))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hn
    rw [common_height_zero_of_not_live η t S β p hn,zero_mul]
  · apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun x : ℂ => heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) * x)
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_live_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _

end CenteredMomentSecondLiveBlock

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSourceAbsoluteEnvelope
open HeckeFamily CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeHeight CenteredMomentPositiveSummability
open CenteredMomentAbsoluteEnergy InversePrincipalEnergy 
local notation "O" => Eisenstein.O

 theorem actual_source_absolute (Q:Finset (Ideal O)) (c:Ideal O→ℂ) (η:Character) (t:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0< K) :
    sourceRestrictedEnergy keep Q c (heightCoeff η t) Φ K≤
      diagonalControl Φ*max 1 K*(∑I∈Q,‖c I‖)^2 := by
  let F:O→ℂ:=fun z=> rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=> c I*heightCoeff η t I) z
  let B:ℝ:=∑I∈Q,‖c I‖
  have hB:0≤ B:=Finset.sum_nonneg (fun I _=> norm_nonneg _)
  have hF (z:O):‖F z‖≤ B:=by
    change ‖rowPolynomial Finset.univ (sourceGenerator Q) (fun I:supportedColumns Q=> c I*heightCoeff η t I) z‖≤∑I∈Q,‖c I‖
    rw [height_source_row η t Q c z]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg (c I)) (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all η CenteredMomentSecondHeightFamily.fixedBadMask 1 z t I)
  have hs:=bounded_radial_summable F B hF keep Φ K hK
  have hh:=hs.tsum_le_tsum (g:=fun z:O=> B^2*‖Φ (‖ringComplex z‖^2/K)‖) (fun z=> by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left (B^2))
  rw [tsum_mul_left] at hh
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg B)).trans_eq (by ring)

end CenteredMomentSourceAbsoluteEnvelope

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondSquarefreeBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => Eisenstein.O

theorem actual_block_from_squarefree_source (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃B:ℝ,0≤ B ∧ ∀r:ℝ,0< r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0< X → 0< Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      lambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0< H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:Ideal O→ℝ,
      (∀L,0≤ E₁ L) → (∀L,0≤ E₂ L) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤ E₁ L*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=> if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤ E₂ L*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=> logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        B*∑L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨B,hB,hbound⟩:=CenteredMomentSecondRadicalBlock.actual_block_from_masked_source W decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let coarse (G:Ideal O) (hg:G≠0) (L:Ideal O):ℝ:=
    SchwartzPlanePoisson.diagonalControl Φ*max 1 H*
      (∑I∈residualPool G hg S,‖if IsCoprime G I ∧ L∣I then β (G*I) else 0‖)^2
  have hcoarse (G:Ideal O) (hg:G≠0) (L:Ideal O):0≤ coarse G hg L:=
    mul_nonneg (mul_nonneg (SchwartzPlanePoisson.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=> if Squarefree L then E₁ L else coarse C hC.1 L
  let F₂:Ideal O→ℝ:=fun L=> if Squarefree L then E₂ L else coarse D hD.1 L
  have hF₁ (L:Ideal O):0≤ F₁ L:=by dsimp [F₁];split_ifs;exact hE₁ L;exact hcoarse C hC.1 L
  have hF₂ (L:Ideal O):0≤ F₂ L:=by dsimp [F₂];split_ifs;exact hE₂ L;exact hcoarse D hD.1 L
  have hsource (G:Ideal O) (hg:G≠0) (L:Ideal O) (χ:RayCharacter) (v:ℝ) (J:ℕ):
      sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool G hg S)
        (fun I=> if IsCoprime G I ∧ L∣I then β (G*I) else 0)
        (heightCoeff (τ χ) v) Φ H≤ coarse G hg L*(1+‖v‖)^(2*J):=by
    have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool G hg S)
      (fun I=> if IsCoprime G I ∧ L∣I then β (G*I) else 0) (τ χ) v
      (nonexceptional η χ Q m A) Φ H hH
    apply hh.trans
    exact le_mul_of_one_le_right (hcoarse G hg L) (one_le_pow₀ (by linarith [norm_nonneg v]))
  have hh:=hbound r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL χ v
      by_cases hs:Squarefree L
      · simpa only [F₁,if_pos hs] using hleft L hL hs χ v
      · simpa only [F₁,if_neg hs] using hsource C hC.1 L χ v J₁)
    (by
      intro L hL χ v
      by_cases hs:Squarefree L
      · simpa only [F₂,if_pos hs] using hright L hL hs χ v
      · simpa only [F₂,if_neg hs] using hsource D hD.1 L χ v J₂)
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
  · simp only [hμ,norm_zero,zero_mul]
  · have hs:=CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hμ
    simp only [F₁,F₂,if_pos hs]

end CenteredMomentSecondSquarefreeBlock

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentMobiusHarmonicMass
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentDivisorBoundary CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

lemma shell_mass (Ds:Finset (Ideal O)) (n:ℤ) (hn:n∈selectedShells Ds) :
    (∑D∈shell Ds n,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤256 := by
  have ht:1≤ dyadicScale n:=
    (selected_scale_bounds Ds (∑D∈Ds,(Ideal.absNorm D:ℝ))
      (fun D hD _=> Finset.single_le_sum (fun D _=> Nat.cast_nonneg _) hD) n hn).1
  have htp:0< dyadicScale n:=zero_lt_one.trans_le ht
  have hcard:=divisor_dyad_card (shell Ds n) (dyadicScale n) ht
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.1)
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.2)
  calc
    _≤∑D∈shell Ds n,1/dyadicScale n:=by
      apply Finset.sum_le_sum
      intro D hd
      have hh:=(shell_member_data Ds n D hd).2.2.2.2.1
      exact div_le_div₀ (by norm_num) (moebius_norm_le_one D) htp hh
    _=((shell Ds n).card:ℝ)/dyadicScale n:=by simp [div_eq_mul_inv]
    _≤256:=(div_le_iff₀ htp).mpr hcard

 theorem full_mass_subpower (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (Ideal.absNorm D:ℝ)≤ Z^B) →
      (∑D∈Ds,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤ C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower B δ hB hδ
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Ds hn
  have he:=sum_norm_moebius_shells Ds (fun D=>1/(Ideal.absNorm D:ℝ))
  simp only [mul_one_div] at he
  rw [he]
  calc
    _≤∑n∈selectedShells Ds,(256:ℝ):=Finset.sum_le_sum (fun n hn=> shell_mass Ds n hn)
    _=((selectedShells Ds).card:ℝ)*256:=by simp
    _≤(C*Z^δ)*256:=mul_le_mul_of_nonneg_right (hZ.2 Ds hn) (by norm_num)
    _=_:=by ring

 theorem actual_divisorPool_mass (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤ Z^B) →
      (∑D∈divisorPool T v,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤ C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn
  exact hZ.2 (divisorPool T v) (fun D hd _=>(divisorPool_nonzero_norm T v hv (Z^B) hn D hd).2)

end CenteredMomentMobiusHarmonicMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter

namespace CenteredMomentSecondHarmonicBudget
open CenteredMomentSecondWindowBudget CenteredMomentMobiusHarmonicMass
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

lemma paired_divisor (J₁ J₂:ℕ) (t E₁ E₂ n:ℝ) (hn:0≤ n) :
    windowBudget J₁ t (E₁/n)*windowBudget J₂ t (E₂/n)=
      (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/n := by
  simp only [windowBudget,Real.sqrt_div' _ hn]
  calc
    _=(Real.sqrt E₁*heightEnvelope t^J₁*profileMoment J₁*
        (Real.sqrt E₂*heightEnvelope t^J₂*profileMoment J₂))/
          (Real.sqrt n*Real.sqrt n):=by ring
    _=_:=by rw [Real.mul_self_sqrt hn]

 theorem actual_divisor_budget (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤ Z^B) →
      ∀J₁ J₂:ℕ,∀t E₁ E₂:ℝ,
      (∑L∈divisorPool T v,‖(moebius L:ℂ)‖*
        (windowBudget J₁ t (E₁/(Ideal.absNorm L:ℝ))*
          windowBudget J₂ t (E₂/(Ideal.absNorm L:ℝ))))≤
      C*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨C,hC,hbound⟩:=actual_divisorPool_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn J₁ J₂ t E₁ E₂
  have he:(∑L∈divisorPool T v,‖(moebius L:ℂ)‖*
      (windowBudget J₁ t (E₁/(Ideal.absNorm L:ℝ))*windowBudget J₂ t (E₂/(Ideal.absNorm L:ℝ))))=
      (∑L∈divisorPool T v,‖(moebius L:ℂ)‖/(Ideal.absNorm L:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro L hL
    rw [paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (hZ.2 T v hv hn)
    (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))

end CenteredMomentSecondHarmonicBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondSummedBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => Eisenstein.O

open Filter
theorem actual_block_from_divisor_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0:ℝ,0< C0 ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀r:ℝ,0< r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      (∀J:sectorPool D hD.1 S,(Ideal.absNorm (J:Ideal O):ℝ)≤ Z^B) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0< X → 0< Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      lambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0< H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=> if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₂/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=> logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨K,hK,hkernel⟩:=CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentSecondHarmonicBudget.actual_divisor_budget B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC0 hD hCD U A hτ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hk:=hkernel r hr η τ t S β C D hC0 hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor
    (fun L=> E₁/(Ideal.absNorm L:ℝ)) (fun L=> E₂/(Ideal.absNorm L:ℝ))
    (fun L=> div_nonneg hE₁ (Nat.cast_nonneg _)) (fun L=> div_nonneg hE₂ (Nat.cast_nonneg _))
    hleft hright
  have hs:=hZ.2 Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
    (fun J _=>(sectorPool_supported D hD.1 S J).1) (fun J _=> hn J) J₁ J₂ t E₁ E₂
  apply hk.trans
  calc
    _≤ K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=mul_le_mul_of_nonneg_left hs hK
    _≤ max 1 K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
          (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    _=_:=by ring

end CenteredMomentSecondSummedBlock

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
