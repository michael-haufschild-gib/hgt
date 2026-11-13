/-
Bad phases at the cusps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.MeanSquare.InitialMeanSquareRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.UniformPolynomialKernels

/-!
# Bad phases at the cusps

Cusp bad phases `cuspBadPhase` as fixed residues and cusp arrays with phase. Completed rows
have a polynomial height bound of fixed degree; dyadic summation extends the completed shell
estimate to bounded finite ideal families.
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

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight
open scoped BigOperators Classical ContDiff

/-- Actual completed rows have a polynomial height bound with degree independent of the source. -/
theorem actual_cusp_fiber_uniform_height
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (a b : ℝ) (ha : 0<a) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃n : ℕ, ∀W : ℝ → ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ K X : ℝ),1≤ K→ 1≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (R F : Ideal O),R∈rows→ Squarefree F→ 
    (∀J∈rows,J≠0 ∧ K/2≤ (Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J : RowIndex m rows R F,IsCoprime (Ideal.span {c}) (rowResidualPart J.val (Ideal.span {m}*F)))→ 
      (∑J : RowIndex m rows R F,
        ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)) (normTwistedSource W θ) X‖^2)≤ 
      (C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)/X)/(Ideal.absNorm (rowPowerfulPart R):ℝ) := by
  obtain ⟨n,hn⟩:=uniform_polynomial_fiber_energy
    (fun W : SupportedSmoothSource a b => normTwistedSource W.val)
    (normTwistedSource_uniform_polynomial_kernel a b ha) δ ε 1
    completedRamifiedStep (fixedCuspLevelBound c hc) hδ hε zero_lt_one
    completedRamifiedStep_gt_one (fixedCuspLevelBound_ge_one c hc)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,henergy⟩:=hn ⟨W,hs,hW⟩
  let S : ℂ:=thetaDerivativeScalar⁻¹*(36*(fixedCuspArrayBound:ℂ))
  refine ⟨1+‖S‖^2*C*(fixedCuspRayCount c hc:ℝ)^2,by positivity,?_⟩
  intro θ K X hK hX m hm rows R F hR hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let G:=uniformTwistedSchwartz W a b ha hs hW θ
  have hG : (G : ℝ → ℂ)=normTwistedSource W θ :=
    funext (uniformTwistedSchwartz_apply W a b ha hs hW θ)
  have hθs : Function.support (normTwistedSource W θ)⊆Set.Icc a b :=
    (normTwistedSource_support W θ).trans hs
  have hθW : ContDiff ℝ ∞ (normTwistedSource W θ) := by
    rw [←hG]
    exact G.smooth ⊤
  let Q:=Ideal.span {m}*F
  have hR0:=(hrows R hR).1
  have hRK:=(hrows R hR).2.2
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  obtain ⟨d,hd⟩:=exists_actual_cusp_fiber m hm rows R F hR0 hF K hrows v Ψ Qbase c hc
    hspan hperiod hnorm hmLam hm2 hbad hcop
  let hupper : ∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K:=
    fun J hJ=>⟨(hrows J hJ).1,(hrows J hJ).2.2⟩
  let ι:=fiberResidualIndex rows R Q K hbad hupper
  have hi:=fiberResidualIndex_injective rows R Q K hbad hupper
  have he:=henergy θ (fixedCuspRayCount c hc) K X hK hX R F Q hR0 hQ hRK
    (one_le_completedResidualScale K R Q hR0 hRK) d
  have hsum : (∑J : RowIndex m rows R F,‖d.value (normTwistedSource W θ) X 1 completedRamifiedStep (ι J)‖^2)≤ 
      ∑k,‖d.value (normTwistedSource W θ) X 1 completedRamifiedStep k‖^2 := by
    calc
      _=∑k∈Finset.univ.image ι,‖d.value (normTwistedSource W θ) X 1 completedRamifiedStep k‖^2 :=
        (Finset.sum_image (fun J _ L _ he=>hi he)).symm
      _≤ _:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _=>sq_nonneg _)
  have heq : (∑J : RowIndex m rows R F,
      ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)) (normTwistedSource W θ) X‖^2)=
      ‖S‖^2*∑J : RowIndex m rows R F,‖d.value (normTwistedSource W θ) X 1 completedRamifiedStep (ι J)‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [hd J (normTwistedSource W θ) a b ha hθs hθW X (lt_of_lt_of_le zero_lt_one hX)]
    have hk : rowResidualPart J.val Q=(ι J).val:=rfl
    rw [hk,ReflectedFiberData.idealValue_at,norm_mul,mul_pow]
  rw [heq]
  apply (mul_le_mul_of_nonneg_left (hsum.trans he) (sq_nonneg ‖S‖)).trans
  let shape:=(1+‖θ‖)^n*(K*(Ideal.absNorm Q:ℝ))^(10*δ+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)/(Ideal.absNorm (rowPowerfulPart R):ℝ)
  have hshape : 0≤  shape:=by dsimp only [shape]; positivity
  calc
    _=(‖S‖^2*C*(fixedCuspRayCount c hc:ℝ)^2)*shape := by dsimp only [shape]; ring
    _≤ (1+‖S‖^2*C*(fixedCuspRayCount c hc:ℝ)^2)*shape :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hshape
    _=_ := by dsimp only [shape,Q]; ring

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight
open scoped BigOperators Classical ContDiff

/-- Summing the powerful and mask fibers gives the completed energy of an entire ideal shell. -/
theorem actual_cusp_shell_uniform_height
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (a b : ℝ) (ha : 0<a) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃n : ℕ, ∀W : ℝ → ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ K X : ℝ),1≤ K→ 1≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (F : Ideal O),Squarefree F→ 
    (∀J∈rows,J≠0 ∧ K/2≤ (Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J∈rows,IsCoprime (Ideal.span {c}) (rowResidualPart J (Ideal.span {m}*F)))→ 
      (∑J∈rows,
        ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) X‖^2)≤ 
      (C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)/X) := by
  obtain ⟨n,hn⟩:=actual_cusp_fiber_uniform_height c hc a b ha δ ε hδ hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hfiber⟩:=hn W hs hW
  obtain ⟨D,hD,houter⟩:=completed_outer_row_small_power ε hε
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro θ K X hK hX m hm rows F hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let f (J : Ideal O):=
    ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) X‖^2
  let B:=(C*(1+‖θ‖)^n)*(K*(Ideal.absNorm Q:ℝ))^(10*δ+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤ B:=by dsimp only [B]; positivity
  have hblocks (A : Ideal O) (hA : A∈rows.image rowPowerfulPart)
      (T : Ideal O) (hT : T∈rows.image (fun I=>rowMaskPart I Q)) :
      (∑I∈completedRowFiber rows Q A T,f I)≤ B/(Ideal.absNorm A:ℝ) := by
    by_cases hempty : completedRowFiber rows Q A T=∅
    · rw [hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
    · obtain ⟨R,hR⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨hRrows,hRA,hRT⟩:=Finset.mem_filter.mp hR
      have hb:=hfiber θ K X hK hX m hm rows R F hRrows hF hrows v Ψ Qbase hspan hperiod hnorm
        hmLam hm2 hbad (fun J=>hcop J.val (Finset.mem_filter.mp J.property).1)
      change (∑J : representativeRowFiber rows R Q,f J.val) ≤ _ at hb
      rw [Finset.sum_coe_sort (s:=representativeRowFiber rows R Q) (f:=f)] at hb
      change (∑I∈representativeRowFiber rows R Q,f I)≤ B/(Ideal.absNorm (rowPowerfulPart R):ℝ) at hb
      simpa only [representativeRowFiber,hRA,hRT] using hb
  have hb:=houter rows Q hQ f B hB hblocks
  have hnormQ : 0<(Ideal.absNorm Q:ℝ):=nonzeroDualIdeal_norm_pos ⟨Q,hQ⟩
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ):=mul_pos (lt_of_lt_of_le zero_lt_one hK) hnormQ
  have hp : (Ideal.absNorm Q:ℝ)^ε≤ (K*(Ideal.absNorm Q:ℝ))^ε:=
    Real.rpow_le_rpow hnormQ.le (le_mul_of_one_le_left hnormQ.le hK) hε.le
  calc
    _≤ D*(Ideal.absNorm Q:ℝ)^ε*B:=hb
    _≤ D*(K*(Ideal.absNorm Q:ℝ))^ε*B:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD.le) hB
    _=_ := by
      dsimp only [B]
      rw [show 10*δ+2*ε=ε+(10*δ+ε) by ring,Real.rpow_add hKQ ε (10*δ+ε)]
      dsimp only [Q]
      ring

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight
open scoped BigOperators Classical ContDiff

/-- Dyadic summation extends the completed shell estimate to every bounded finite ideal family. -/
theorem actual_cusp_rows_uniform_height
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (a b : ℝ) (ha : 0<a) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃n : ℕ, ∀W : ℝ → ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ K X : ℝ),1≤ K→ 1≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (F : Ideal O),Squarefree F→ 
    (∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J∈rows,IsCoprime (Ideal.span {c}) (rowResidualPart J (Ideal.span {m}*F)))→ 
      (∑J∈rows,
        ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) X‖^2)≤ 
      (C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)/X) := by
  obtain ⟨n,hn⟩:=actual_cusp_shell_uniform_height c hc a b ha δ ε hδ hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hS⟩:=hn W hs hW
  let s:=10*δ+2*ε
  refine ⟨C*(16*(2:ℝ)^s),by positivity,?_⟩
  intro θ K X hK hX m hm rows F hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  have hQ : Q≠0:=mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  have hnormQ : 0<(Ideal.absNorm Q:ℝ):=nonzeroDualIdeal_norm_pos ⟨Q,hQ⟩
  let f (J : Ideal O):=
    ‖completedT (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) X‖^2
  have hd (j : ℕ) :
      (∑I∈completedRowDyad rows j,f I)≤ 
        (C*(1+‖θ‖)^n)*((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := by
    exact hS θ ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX m hm (completedRowDyad rows j) F hF
      (completedRowDyad_bounds rows j (fun I hI=>(hrows I hI).1)) v Ψ Qbase
      hspan hperiod hnorm hmLam hm2 hbad
      (fun I hI=>hcop I (Finset.mem_filter.mp hI).1)
  have hb:=completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) (by dsimp only [s]; positivity)
    hK (lt_of_lt_of_le zero_lt_one hX) hnormQ
  calc
    _=∑j∈Finset.range (completedRowDyadicLength K+1),∑I∈completedRowDyad rows j,f I:=
      (completedRowDyad_sum rows K (le_trans zero_le_one hK) (fun I hI=>(hrows I hI).2) f).symm
    _≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
        (C*(1+‖θ‖)^n)*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using hd j
    _=(C*(1+‖θ‖)^n)*∑j∈Finset.range (completedRowDyadicLength K+1),
        ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X):=(Finset.mul_sum _ _ _).symm
    _≤ (C*(1+‖θ‖)^n)*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)):=
      mul_le_mul_of_nonneg_left hb (show 0≤C*(1+‖θ‖)^n by positivity)
    _=_:=by dsimp only [s,Q]; ring

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic
open scoped BigOperators Classical ContDiff

/-- The short cube inverse has a uniform arithmetic energy bound on actual ideal rows. -/
theorem actual_short_rows_uniform_height
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (a b : ℝ) (ha : 0<a) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃n : ℕ, ∀W : ℝ → ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ K X H₀ : ℝ),1≤ K→ 1≤ H₀→ H₀^3≤ X→ ∀(m : O),m≠0→ 
    ∀(rows : Finset (Ideal O)) (F : Ideal O),Squarefree F→ 
    (∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K)→ 
    ∀(v : Oˣ) (Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀J∈rows,IsCoprime (Ideal.span {c}) (rowResidualPart J (Ideal.span {m}*F)))→ 
      (∑J∈rows,
        ‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) X H₀‖^2)≤ 
      ((C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
          (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2 := by
  obtain ⟨n,hn⟩:=actual_cusp_rows_uniform_height c hc a b ha δ ε hδ hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hcompleted⟩:=hn W hs hW
  refine ⟨C,hC,?_⟩
  intro θ K X H₀ hK hH₀ hX m hm rows F hF hrows v Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let Q:=Ideal.span {m}*F
  let row (J : rows):=rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val)
  let E:=(C*(1+‖θ‖)^n)*(K*(Ideal.absNorm Q:ℝ))^(10*δ+2*ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)*H₀^3/X)
  have hX0 : 0<X:=(pow_pos (lt_of_lt_of_le zero_lt_one hH₀) 3).trans_le hX
  have hE : 0≤ E:=by dsimp only [E]; positivity
  have hWc : HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hs)
  have hbound (H : Ideal O) (hH : H∈shortCubeRange H₀) :
      (∑J : rows,‖completedIdealT (row J) (normTwistedSource W θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤ E := by
    have hh:=(mem_shortCubeRange H₀ H).mp hH
    have hn : 0<(Ideal.absNorm H:ℝ):=nonzeroDualIdeal_norm_pos ⟨H,hh.1⟩
    have hp : (Ideal.absNorm H:ℝ)^3≤ H₀^3:=pow_le_pow_left₀ hn.le hh.2.le 3
    have hY : 1≤ X/(Ideal.absNorm H:ℝ)^3:=
      (le_div_iff₀ (pow_pos hn 3)).mpr (by simpa only [one_mul] using hp.trans hX)
    have hb:=hcompleted θ K (X/(Ideal.absNorm H:ℝ)^3) hK hY m hm rows F hF hrows v Ψ Qbase
      hspan hperiod hnorm hmLam hm2 hbad hcop
    simp_rw [completedIdealT_eq_completedT _ (normTwistedSource W θ) hWc _ (div_pos hX0 (pow_pos hn 3))]
    dsimp only [row]
    rw [Finset.sum_coe_sort (s:=rows) (f:=fun J => ‖completedT (rowTwist Ψ m (cubicIdealGenerator F)
      ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity : 0≤ K^2*(Ideal.absNorm Q:ℝ))) hX0.le
  have hb:=short_completed_energy row
    (fun J n=>rowTwist_norm Ψ hnorm m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J.val) n)
    (normTwistedSource W θ) X H₀ E hE hbound
  dsimp only [row] at hb
  rw [Finset.sum_coe_sort (s:=rows) (f:=fun J =>
    ‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) ((v:O)*cubicIdealGenerator J)) (normTwistedSource W θ) X H₀‖^2)] at hb
  exact hb

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight CompletedUnitRows
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- The short completed estimate is uniform over the unit sectors of actual element rows. -/
theorem actual_elements_uniform_height
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (a b : ℝ) (ha : 0<a) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃n : ℕ, ∀W : ℝ → ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ K X H₀ : ℝ),1≤ K→ 1≤ H₀→ H₀^3≤ X→ ∀(m : O),m≠0→ 
    ∀(T : Finset O) (F : Ideal O),Squarefree F→ 
    (∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤ K)→ 
    ∀(Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀z∈T,IsCoprime (Ideal.span {c}) (rowResidualPart (Ideal.span {z}) (Ideal.span {m}*F)))→ 
      (∑z∈T,‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) z) (normTwistedSource W θ) X H₀‖^2)≤ 
      ((C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
          (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2 := by
  obtain ⟨n,hn⟩:=actual_short_rows_uniform_height c hc a b ha δ ε hδ hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hrow⟩:=hn W hs hW
  refine ⟨((Fintype.card Oˣ:ℝ)+1)*C,by positivity,?_⟩
  intro θ K X H₀ hK hH₀ hX m hm T F hF hT Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let rows:=T.image (fun z=>Ideal.span {z})
  have hrows:=image_span_nonzero_norm T K hT
  have hcoprows (I : Ideal O) (hI : I∈rows) :
      IsCoprime (Ideal.span {c}) (rowResidualPart I (Ideal.span {m}*F)) := by
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact hcop z hz
  let E:=((C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
    (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
      (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2
  have hX0 : 0<X:=(pow_pos (lt_of_lt_of_le zero_lt_one hH₀) 3).trans_le hX
  have hE : 0≤ E:=by dsimp only [E]; positivity
  have hu (u : Oˣ) :
      (∑I∈rows,‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F)
        ((u:O)*cubicIdealGenerator I)) (normTwistedSource W θ) X H₀‖^2)≤ E:=
    hrow θ K X H₀ hK hH₀ hX m hm rows F hF hrows u Ψ Qbase hspan hperiod hnorm
      hmLam hm2 hbad hcoprows
  have hb:=sum_elements_le_units_bound T
    (fun z=>‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) z) (normTwistedSource W θ) X H₀‖^2)
    (fun z=>sq_nonneg _) E hE hu
  exact hb.trans_eq (by dsimp only [E]; ring)

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight CompletedUnitRows
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- Norm twists of actual completed rows satisfy a common polynomial height bound. -/
theorem actual_elements_uniform_twist
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (a b : ℝ) (ha : 0<a) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃n : ℕ, ∀W : ℝ → ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ K X H₀ : ℝ),1≤ K→ 1≤ H₀→ H₀^3≤ X→ ∀(m : O),m≠0→ 
    ∀(T : Finset O) (F : Ideal O),Squarefree F→ 
    (∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤ K)→ 
    ∀(Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀z∈T,IsCoprime (Ideal.span {c}) (rowResidualPart (Ideal.span {z}) (Ideal.span {m}*F)))→ 
      (∑z∈T,‖shortCompletedSum (SecondPassArithmetic.normHeightTwist (rowTwist Ψ m (cubicIdealGenerator F) z) θ) W X H₀‖^2)≤ 
      ((C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
          (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2 := by
  obtain ⟨n,hn⟩:=actual_elements_uniform_height c hc a b ha δ ε hδ hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hn W hs hW
  refine ⟨C,hC,?_⟩
  intro θ K X H₀ hK hH₀ hX m hm T F hF hT Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  have hX0 : 0<X:=(pow_pos (lt_of_lt_of_le zero_lt_one hH₀) 3).trans_le hX
  simp_rw [shortCompletedSum_normHeight_norm _ W θ X H₀ hX0]
  exact h θ K X H₀ hK hH₀ hX m hm T F hF hT Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight CompletedUnitRows
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic CanonicalCoefficientClass
open scoped BigOperators Classical ContDiff

/-- The rank margin absorbs short cube scales uniformly over the fixed ray-character orbit. -/
theorem actual_fixed_mask_short_average
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (base : O →* ℂ) (hbase : ∀x y : O,x-y∈Qbase → base x=base y)
    (hbaseNorm : ∀x,‖base x‖≤1)
    (a b η ε : ℝ) (ha : 0<a) (hη : 0<η) (hε : 0<ε) :
    ∃n : ℕ,∀W : ℝ → ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀θ Z K X F : ℝ,1≤Z → 1≤K → 1≤F → F≤Z^(1/1000:ℝ) →
    ∀m : O,m≠0 →
    K*(Ideal.absNorm (Ideal.span {m*excludedGenerator S}):ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀T : Finset O,(∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤K) →
    ∀Ψ : O →* ℂ,IsBaseRayTwist base Ψ →
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
          (m*excludedGenerator S) (cubicIdealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)/F≤
      (C*(1+‖θ‖)^n)*(K*(Ideal.absNorm (Ideal.span {m*excludedGenerator S}):ℝ)*F)^η*K*Z^ε := by
  obtain ⟨n,hn⟩:=actual_elements_uniform_twist c hc a b ha (η/20) (η/4) (by positivity) (by positivity)
  have hexp : 10*(η/20)+2*(η/4)=η:=by ring
  let D:=descentLatticeConstant*Real.exp 1*(1+1/(ε/2))
  have hL:=descentLatticeConstant_pos
  have hD : 0<D:=by dsimp only [D]; positivity
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hn W hs hW
  refine ⟨2*descentLatticeConstant*C*D^2,by positivity,?_⟩
  intro θ Z K X F hZ hK hF hFZ m hm hmargin T hT Ψ hΨ
  let G : Ideal O:=Ideal.span {m*excludedGenerator S}
  let H₀:=Z^(1/1000:ℝ)
  have hmask:=excluded_mask_inputs S hSp hbad c hc hsupport m hm (1:Ideal O)
  have hG : G≠0:=Ideal.span_singleton_eq_bot.not.mpr hmask.1
  have hNG : 1≤(Ideal.absNorm G:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz=>hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hZ0 : 0<Z:=lt_of_lt_of_le zero_lt_one hZ
  have hH₀ : 1≤H₀:=Real.one_le_rpow hZ (by norm_num)
  have hsc:=short_cube_scales Z K (Ideal.absNorm G:ℝ) X F H₀ hZ hK hNG hF hFZ hH₀ le_rfl hmargin
  have hH₀0 : 0<H₀:=lt_of_lt_of_le zero_lt_one hH₀
  have hXcube : H₀^3≤X:=(by simpa only [one_mul] using
    (le_div_iff₀ (pow_pos hH₀0 3)).mp hsc.1)
  have hX : 0<X:=(pow_pos hH₀0 3).trans_le hXcube
  let L:=descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ)
  have hL0 : 0≤L:=by dsimp only [L]; positivity
  have hlog : L≤D*Z^(ε/2):=by
    have hHZ : H₀≤Z:=by
      simpa only [H₀,Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hZ (show (1/1000:ℝ)≤1 by norm_num)
    have hb:=descent_normLogBin_small_power (ε/2) (by positivity) H₀ hH₀
    calc
      L≤descentLatticeConstant*Real.exp 1*((1+1/(ε/2))*H₀^(ε/2)):=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _=D*H₀^(ε/2):=by dsimp only [D]; ring
      _≤D*Z^(ε/2):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hH₀0.le hHZ (by positivity)) hD.le
  have hlog2 : L^2≤D^2*Z^ε:=by
    have hp : (Z^(ε/2))^2=Z^ε:=by
      rw [pow_two,←Real.rpow_add hZ0]
      congr 1
      ring
    simpa only [mul_pow,hp] using pow_le_pow_left₀ hL0 hlog 2
  let A:=(C*(1+‖θ‖)^n)*(K*(Ideal.absNorm G:ℝ)*F)^η
  have hA : 0≤A:=by dsimp only [A]; positivity
  have hfbound (f : idealRange F) :
      (∑z∈T,‖shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        (m*excludedGenerator S) (cubicIdealGenerator f.val) z) W X H₀‖^2)≤
        (A*(2*K))*(D^2*Z^ε) := by
    have hf:=(mem_idealRange.mp f.property)
    have hi:=excluded_mask_inputs S hSp hbad c hc hsupport m hm f.val
    have hb:=h θ K X H₀ hK hH₀ hXcube (m*excludedGenerator S) hi.1 T f.val hf.1.2.1 hT
      Ψ Qbase hspan (baseRayTwist_periodic Qbase h4 base Ψ hΨ hbase)
      (hΨ.norm_le hbaseNorm) hi.2.1 hi.2.2.1 hi.2.2.2.1 (fun z _=>hi.2.2.2.2 (Ideal.span {z}))
    simp_rw [rowTwist_normHeight]
    rw [hexp] at hb
    apply hb.trans
    have hN : (Ideal.absNorm (G*f.val):ℝ)=(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ):=by
      rw [map_mul,Nat.cast_mul]
    have hp : (K*(Ideal.absNorm (G*f.val):ℝ))^η≤(K*(Ideal.absNorm G:ℝ)*F)^η:=by
      rw [hN]
      apply Real.rpow_le_rpow (by positivity) _ hη.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf.2
        (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
    have hshape : K+K^2*(Ideal.absNorm (G*f.val):ℝ)*H₀^3/X≤2*K:=by
      rw [hN]
      have hb : K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))*H₀^3/X≤
          K^2*(Ideal.absNorm G:ℝ)*F*H₀^3/X:=by
        calc
          _=(K^2*(Ideal.absNorm G:ℝ)*H₀^3/X)*(Ideal.absNorm f.val:ℝ):=by ring
          _≤(K^2*(Ideal.absNorm G:ℝ)*H₀^3/X)*F:=
            mul_le_mul_of_nonneg_left hf.2 (by positivity)
          _=_:=by ring
      linarith only [hb,hsc.2]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hshape (by positivity) hA)
      hlog2 (sq_nonneg _) (mul_nonneg hA (by positivity))
  have hcount : ((idealRange F).card:ℝ)≤descentLatticeConstant*F:=
    descent_ideal_count _ F hF (fun f hf=>(mem_idealRange.mp hf).1.2.1.ne_zero)
      (fun f hf=>(mem_idealRange.mp hf).2)
  calc
    _≤((idealRange F).card:ℝ)*((A*(2*K))*(D^2*Z^ε))/F:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (Finset.sum_le_sum (fun f _=>hfbound f)).trans_eq (by simp)
    _≤(descentLatticeConstant*F)*((A*(2*K))*(D^2*Z^ε))/F:=by
      gcongr
    _=_:=by
      dsimp only [A,G]
      field_simp

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedHeight CompletedUnitRows
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic CanonicalCoefficientClass FirstPassCubeLabels
open scoped BigOperators Classical ContDiff

/-- Actual periodic rows satisfy the short part of the canonical rank recurrence. -/
theorem actual_canonical_short_state
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (base : O →* ℂ) (hbase : ∀x y : O,x-y∈Qbase → base x=base y)
    (hbaseNorm : ∀x,‖base x‖≤1)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) :
    ∃n : ℕ,∀W : ℝ → ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ Z η : ℝ) (Ψ : O →* ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F K : ℝ),
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
    1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
    2*‖ringComplex (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (cubicIdealGenerator I) z)
        W X (if F<Z^(1/1000:ℝ) then Z^(1/1000:ℝ) else 0)) K≤
      (C*(1+‖θ‖)^n)*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨n,hn⟩:=actual_fixed_mask_short_average S hSp hbad Qbase h4 c hc hspan hsupport
    base hbase hbaseNorm a b ε ε ha hε hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hn W hs hW
  refine ⟨2*C,by positivity,?_⟩
  intro θ Z η Ψ m labels X F K hstate hZ hZbig hη hbudget hfixed
  have hK : 0<K:=zero_lt_one.trans_le hstate.row_ge_one
  have hF : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  by_cases hsmall : F<Z^(1/1000:ℝ)
  · rw [if_pos hsmall]
    obtain ⟨hG,hbadG,hlabels,hmass,hmargin⟩:=canonicalShortState_geometry
      S hSp hbad base Z η Ψ m labels X F K hstate hZ hZbig hη hbudget hfixed
    let G : Ideal O:=Ideal.span {m*excludedGenerator S}
    let T:=(firstFrequencyDisk (2*K)).erase 0
    have hT (z : O) (hz : z∈T) : z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤2*K:=by
      refine ⟨(Finset.mem_erase.mp hz).1,?_⟩
      rw [←ringComplex_norm_sq_eq_absNorm_span]
      exact (mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
    let P (I : Ideal O) (z : O):=shortCompletedSum
      (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (cubicIdealGenerator I) z)
      W X (Z^(1/1000:ℝ))
    have hb:=h θ Z (2*K) X F hZ (by linarith [hstate.row_ge_one]) hstate.label_ge_one hsmall.le
      m hstate.mask_ne_zero hmargin T hT Ψ hstate.coefficient
    have hsum : (∑f : idealRange F,∑z∈T,‖P f.val z‖^2)≤
        ((C*(1+‖θ‖)^n)*((2*K)*(Ideal.absNorm G:ℝ)*F)^ε*(2*K)*Z^ε)*F:=
      (div_le_iff₀ hF).mp hb
    have hE : rowFamilyEnergy labels P K≤∑f : idealRange F,∑z∈T,‖P f.val z‖^2:=by
      rw [rowFamilyEnergy_eq_sum labels P K hK,
        Finset.sum_coe_sort (s:=idealRange F) (f:=fun I=>∑z∈T,‖P I z‖^2)]
      calc
        _≤∑I∈labels,∑z∈T,‖P I z‖^2:=by
          apply Finset.sum_le_sum
          intro I hI
          apply Finset.sum_le_sum
          intro z hz
          apply mul_le_of_le_one_left (sq_nonneg _)
          change sieveBump (‖ringComplex z‖^2/K)≤1
          exact sieveBump.le_one
        _≤_:=Finset.sum_le_sum_of_subset_of_nonneg hlabels (fun I _ _=>
          Finset.sum_nonneg (fun z _=>sq_nonneg _))
    have hE' : rowFamilyEnergy labels P K≤
        ((2*C)*(1+‖θ‖)^n)*1*((2*K)*(Ideal.absNorm G:ℝ)*F)^ε*(K*F)*Z^ε:=
      (hE.trans hsum).trans_eq (by ring)
    have hFZ : F≤Z^3:=by
      apply hsmall.le.trans
      rw [←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
    have hNG : 1≤(Ideal.absNorm G:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz=>hG (Ideal.absNorm_eq_zero_iff.mp hz))
    have hscalar:=shortEnergy_scalar_normalization (2*C) ((1+‖θ‖)^n) 1 Z K X F
      (Ideal.absNorm G:ℝ) ε (by positivity) (by positivity) (by norm_num) hZ hK.le
      hstate.column_pos hF.le hNG hε.le hFZ hmass hmargin
    exact (mul_le_mul_of_nonneg_left hE' (mul_nonneg (by norm_num) hstate.column_pos.le)).trans (by simpa only [mul_one] using hscalar)
  · rw [if_neg hsmall,rowFamilyEnergy_eq_sum labels _ K hK]
    simp only [shortCompletedSum_nonpos _ _ _ _ le_rfl,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
      mul_zero,Finset.sum_const_zero]
    positivity

end CanonicalRowCompletion.ActualCuspFiber

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem progressingCanonicalFamily_energy
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (labels : Finset (Ideal O)) (Ψ : O→*ℂ) (m : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u|≤columnWindowRadius a b→ V u=1)
    (X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hX : 0<X) (hK : 0<K) (hE : 0≤E) (hD : b*X≤D) :
    let F:=outsideSquarefreeIdeals S D
    let hF:=outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀j∈cubeLogRange b X,
      let B:=normLogScale j
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D b X j)
      Q'.Nonempty → ∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (cubicIdealGenerator I)
          (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) (X/B^3) T)) z) K≤
        E*(1+|oldHeight+ξ|)^(2*J)) →
    rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
      m (cubicIdealGenerator I) z W X) K≤
    2*X*rowFamilyEnergy labels (fun I z=>
      shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀) K+
    2*((cubeLogRange b X).card:ℝ)^2*E*(1+|oldHeight|)^(2*J)*
      (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by
  dsimp only
  let F:=outsideSquarefreeIdeals S D
  have hF:=outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro hsource
  let T:=E*(1+|oldHeight|)^(2*J)*(∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2
  have hT : 0≤T := by dsimp only [T];positivity
  let binEnergy:=fun j=>rowFamilyEnergy labels (fun I z=>
    outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) (normHeightTwist Ψ oldHeight)
      m (cubicIdealGenerator I) z W X H₀) K
  have hbin (j : ℕ) (hj : j∈cubeLogRange b X) : X*binEnergy j≤T := by
    by_cases hnon : (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · apply progressingCanonicalBin_energy S D hbad (activeCubeLogBin S D b X j) labels Ψ m W
        a b ha hs hW V hV (normLogScale j) (X/(normLogScale j)^3) X H₀ K E oldHeight J
        (normLogScale_pos j) (div_pos hX (pow_pos (normLogScale_pos j) _))
        (by field_simp [(normLogScale_pos j).ne']) hK hE
        (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).1)
        (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).2)
      exact hsource j hj hnon
    · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hnon
      have heq : (fun I z=>outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j)
          (normHeightTwist Ψ oldHeight) m (cubicIdealGenerator I) z W X H₀)=(fun _ _=>0) := by
        funext I z
        exact outsideCanonicalBin_zero_of_empty_filter S D hbad _ _ m _ z W X H₀ hempty
      dsimp only [binEnergy]
      rw [heq]
      simpa only [rowFamilyEnergy,nonzeroRowMajorantSum,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
        Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hT
  have hsum : X*∑j∈cubeLogRange b X,binEnergy j≤((cubeLogRange b X).card:ℝ)*T := by
    simpa only [Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hbin
  have hwhole:=outsideCanonicalRow_family_binned_energy S D hbad hSp (normHeightTwist Ψ oldHeight)
    m labels W hWc b X H₀ K hb hX hK (fun x hx=>(hs hx).2) hD
  calc
    _ ≤ 2*X*(rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀) K+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,binEnergy j) := hwhole
    _ = 2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀) K+
        (2*((cubeLogRange b X).card:ℝ))*(X*∑j∈cubeLogRange b X,binEnergy j) := by ring
    _ ≤ 2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) z) W X H₀) K+
        (2*((cubeLogRange b X).card:ℝ))*(((cubeLogRange b X).card:ℝ)*T) := by gcongr
    _ = _ := by dsimp only [T];ring

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem progressingCanonicalFamily_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→ |t|≤M) (hV : ∀t,V t≠0→ |t|≤Nv)
    (hWin : ∀t,g t≠0→ V t=1)
    (hgOne : ∀u,|u|≤columnWindowRadius (Real.exp (-A)) (Real.exp A)→ g u=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η≤(1:ℝ)/1000) (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→ |t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→ |t|≤M+7) ∧
      ∀(W : ℝ→ℂ) (hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A))
      (hW : ContDiff ℝ ∞ W), HasCompactSupport W →
      ∃C : ℝ,0≤C ∧
      ∀(S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : O→*ℂ) (Z : ℝ) (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 → 1≤E →
      Real.exp A*X≤D →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_good P hP) (fun _=>1) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_good P hP) (fun _=>1) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
        m (cubicIdealGenerator I) z W X) K≤
      2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (cubicIdealGenerator I) z)
          W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K+
      C*(X*F)^2*Z^(η+17*deltaLoss+39*ε)*E*(1+|oldHeight|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩:=
    progressingCanonicalBin_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cb,hCb,hcard⟩:=cubeLogRange_sq_small_power (Real.exp A) ε (Real.exp_pos _).le hε
  refine ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro W hs hW hWc
  let moment:=∫ξ : ℝ,‖reopeningCoefficient W (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hs hW ξ‖*(1+|ξ|)^J
  refine ⟨2*Cb*C₀*moment^2,by positivity,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE hD
  dsimp only
  let P:=outsideSquarefreeIdeals S D
  have hP:=outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih
  have hsource:=hstep S D hbad hSp base Z Ψ m labels X F K E oldHeight
    hstate hbase hZ hZbig hX hXZ hFZ hE ih
  have hwhole:=progressingCanonicalFamily_energy S D hbad hSp labels Ψ m W
    (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) (Real.exp_pos _).le hs hW hWc
    g hgOne X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0) K
    (C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E) oldHeight J hstate.column_pos
    (zero_lt_one.trans_le hstate.row_ge_one) (by positivity) hD hsource
  have hcount:=hcard X Z hstate.column_pos.le hZ.le hXZ
  have hpower : Z^ε*Z^(η+17*deltaLoss+38*ε)=Z^(η+17*deltaLoss+39*ε) := by
    rw [←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    ring
  apply hwhole.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 2*(Cb*Z^ε)*(C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E)*(1+|oldHeight|)^(2*J)*moment^2 := by
      change 2*((cubeLogRange (Real.exp A) X).card:ℝ)^2*
        (C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E)*(1+|oldHeight|)^(2*J)*moment^2≤_
      gcongr
    _ = (2*Cb*C₀*moment^2)*(X*F)^2*(Z^ε*Z^(η+17*deltaLoss+38*ε))*E*(1+|oldHeight|)^(2*J) := by ring
    _ = _ := by rw [hpower]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open SchwartzPlanePoisson.CanonicalQuadraticSieve CanonicalCubeSeparation JointLogSeparation
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The actual short rows and completed long branches give the canonical rank step. -/
theorem canonicalLog_actual_step
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (A : ℝ) (hA : 0≤A) (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) :
    ∃d : ℕ,∀J : ℕ,d≤2*J →
    ∃child : Bool→Bool→ℝ→ℂ,
      (∀side neg,ContDiff ℝ ∞ (child side neg)) ∧
      (∀side neg s,child side neg s≠0→ |s|≤2*A+11) ∧
      ∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→ |s|≤A) →
      ∃C : ℝ,0≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F K E t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖ringComplex (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      1≤X → Real.exp A*X≤D → 1≤E →
      (∀side neg (Ψ' : O→*ℂ) (m' : O) (labels' : Finset (Ideal O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏P∈S,P) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        outsideLogEnergy S D hbad (normHeightTwist Ψ' s) m' labels' (child side neg) X' K'≤
          E*(X'*F')^2*(1+‖s‖)^(2*J)) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
  obtain ⟨d,hshort⟩:=ActualCuspFiber.actual_canonical_short_state S hSp hbad
    Qbase h4 c hc hspan hsupport base hperiod hbase
    (Real.exp (-A)) (Real.exp A) η (Real.exp_pos _) hη
  refine ⟨d,?_⟩
  intro J hJ
  obtain ⟨g,v,hgc,hvc,hgone,hgb,hwin,hvb⟩:=fixed_reopening_profiles A hA
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  obtain ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hlarge⟩:=
    progressingCanonicalFamily_closed_step g v A (2*A+4) (2*A+5) (by linarith) (by linarith)
      hgb hvb hwin hgone η η η hη hη hη hηsmall hbudget' J
  let child : Bool→Bool→ℝ→ℂ:=fun side neg=>
    orientedLogProfile neg ((if side then w₁ else w₂) (if neg then 5 else 6))
  have hcs : ∀side neg,ContDiff ℝ ∞ (child side neg) := by
    intro side neg
    cases side <;> cases neg
    · exact hws₂ 6
    · exact Complex.conjCLE.contDiff.comp (hws₂ 5)
    · exact hws₁ 6
    · exact Complex.conjCLE.contDiff.comp (hws₁ 5)
  have hcb : ∀side neg s,child side neg s≠0→ |s|≤2*A+11 := by
    intro side neg s hn
    have hnorm (w : Fin 7→ℝ→ℂ) (hw : ∀i t,w i t≠0→ |t|≤(2*A+4)+7)
        (i : Fin 7) (hi : w i s≠0) : |s|≤2*A+11 := by
      have hh:=hw i s hi
      linarith
    cases side <;> cases neg
    · exact hnorm w₂ hwb₂ 6 hn
    · apply hnorm w₂ hwb₂ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
    · exact hnorm w₁ hwb₁ 6 hn
    · apply hnorm w₁ hwb₁ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
  refine ⟨child,hcs,hcb,?_⟩
  intro V hVs hV
  let W : ℝ→ℂ:=radialFromLog V hVs A hV
  have hW : ContDiff ℝ ∞ W:=(radialFromLog V hVs A hV).smooth ⊤
  have hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A):=
    fun s hs=>radialFromLog_support V hVs A hV s hs
  obtain ⟨Cs,hCs,hsmall⟩:=hshort W hs hW
  obtain ⟨Cl,hCl,hlong⟩:=hlarge W hs hW (radialFromLog_hasCompactSupport V hVs A hV)
  refine ⟨Cs+Cl,add_nonneg hCs hCl,?_⟩
  intro D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hD hE ih
  obtain ⟨hXZ,hFZ⟩:=canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
    hZbig hX hstate.label_ge_one hstate.mass_le
  have hsbound:=hsmall t Z η Ψ m labels X F K hstate hZ.le hZbig hη.le hbudget hfixed
  have hb:=hlong S D hbad hSp base Z Ψ m labels X F K E t hstate hbase hZ hZbig
    hX hXZ hFZ hE hD
  dsimp only at hb
  have hlbound:=hb (by
    intro side Ψ' m' labels' X' F' K' hs' hr s
    exact ⟨ih side true Ψ' m' labels' X' F' K' hs' hr s,
      ih side false Ψ' m' labels' X' F' K' hs' hr s⟩)
  have he : η+17*η+39*η=57*η:=by ring
  rw [he] at hlbound
  have hp : Z^(7*η-(1:ℝ)/40)≤Z^(57*η):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have ht : (1+|t|)^d≤(1+|t|)^(2*J):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hs' : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ t) (m*excludedGenerator S) (cubicIdealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      Cs*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
    calc
      _ ≤ Cs*(X*F)^2*Z^(7*η-(1:ℝ)/40)*(1+|t|)^d:=by simpa only [Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hsbound
      _ ≤ Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=by gcongr
      _ ≤ (Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J))*E:=
        le_mul_of_one_le_right (by positivity) hE
      _ = _:=by ring
  rw [outsideLogEnergy_eq_completed S D hbad (normHeightTwist Ψ t) m labels V hVs A hV X K hstate.column_pos]
  exact hlbound.trans ((add_le_add hs' le_rfl).trans_eq (by ring))

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open SchwartzPlanePoisson.CanonicalQuadraticSieve CanonicalCubeSeparation JointLogSeparation
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Finite rank induction closes the actual canonical logarithmic energy. -/
theorem outsideLogEnergy_finite_rank
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (r : ℕ) :
    ∀(A : ℝ),0≤A → ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V →
    (∀s,V s≠0→ |s|≤A) → ∃C : ℝ,1≤C ∧
    ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ) (m : O) (labels : Finset (Ideal O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖ringComplex (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      fixedDepthRank Z K≤r → Real.exp (radiusIter A r)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^(57*η*(r:ℝ))*(X*F)^2*(1+|t|)^d := by
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  induction r with
  | zero =>
    intro A hA
    refine ⟨0,?_⟩
    intro V hVs hV
    obtain ⟨C,hC,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget'
      (Or.inl (Nat.eq_zero_of_le_zero hr))
    simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,pow_zero] using
      hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (sq_nonneg (X*F)))
  | succ r ih =>
    intro A hA
    obtain ⟨dc,hchild⟩:=ih (2*A+11) (by linarith)
    obtain ⟨ds,hstep⟩:=canonicalLog_actual_step S hSp hbad base hbase Qbase h4 c hc hspan hsupport hperiod A hA η hη hηsmall hbudget
    let J : ℕ:=dc+ds
    have hdchild : dc≤2*J:=by dsimp [J];omega
    have hdstep : ds≤2*J:=by dsimp [J];omega
    obtain ⟨child,hcs,hcb,hparent⟩:=hstep J hdstep
    choose childC hchildC using (fun side neg=>hchild (child side neg) (hcs side neg) (hcb side neg))
    have hcnonneg (side neg : Bool) : 0≤childC side neg:=zero_le_one.trans (hchildC side neg).1
    let E0 : ℝ:=1+∑side : Bool,∑neg : Bool,childC side neg
    have hE0 : 1≤E0:=by
      have hs : 0≤∑side : Bool,∑neg : Bool,childC side neg:=
        Finset.sum_nonneg (fun side _=>Finset.sum_nonneg (fun neg _=>hcnonneg side neg))
      exact le_add_of_nonneg_right hs
    have hcE (side neg : Bool) : childC side neg≤E0:=by
      have h1 : childC side neg≤∑j : Bool,childC side j:=
        Finset.single_le_sum (fun j _=>hcnonneg side j) (Finset.mem_univ neg)
      have h2 : (∑j : Bool,childC side j)≤∑i : Bool,∑j : Bool,childC i j:=
        Finset.single_le_sum (fun i _=>Finset.sum_nonneg (fun j _=>hcnonneg i j)) (Finset.mem_univ side)
      exact h1.trans (h2.trans (le_add_of_nonneg_left zero_le_one))
    refine ⟨2*J,?_⟩
    intro V hVs hV
    obtain ⟨Ct,hCt,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    obtain ⟨Cp,hCp,hp⟩:=hparent V hVs hV
    let C : ℝ:=1+Ct+Cp*E0
    have hC : 1≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have htC : Ct≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have hpC : Cp*E0≤C:=by dsimp [C];linarith
    refine ⟨C,hC,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hZ0 : 0<Z:=zero_lt_one.trans hZ
    have hpow : 1≤Z^(57*η*((r+1:ℕ):ℝ)):=
      Real.one_le_rpow hZ.le (by positivity)
    have hheight : 1≤(1+|t|)^(2*J):=one_le_pow₀ (by linarith [abs_nonneg t])
    by_cases hstop : fixedDepthRank Z K=0 ∨ X≤1
    · have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget' hstop
      apply hb.trans
      calc
        Ct*(X*F)^2≤C*(X*F)^2:=mul_le_mul_of_nonneg_right htC (sq_nonneg _)
        _ ≤ C*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by
          calc
            _ ≤ (C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)):=
              le_mul_of_one_le_right (by positivity) hpow
            _ ≤ ((C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)))*(1+|t|)^(2*J):=
              le_mul_of_one_le_right (by positivity) hheight
            _ = _:=by ring
    · have hX : 1≤X:=(lt_of_not_ge (fun hh=>hstop (Or.inr hh))).le
      have hXZ : X≤Z^3:=(canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
        hZbig hX hstate.label_ge_one hstate.mass_le).1
      have hDparent : Real.exp A*X≤D:=
        common_pool_parent A Z X D (r+1) hA hZ0.le hstate.column_pos.le hXZ hD
      let E : ℝ:=E0*Z^(57*η*(r:ℝ))
      have hEr : 1≤Z^(57*η*(r:ℝ)):=Real.one_le_rpow hZ.le (by positivity)
      have hE : 1≤E:=by
        change 1≤E0*Z^(57*η*(r:ℝ))
        simpa only [one_mul] using mul_le_mul hE0 hEr zero_le_one (zero_le_one.trans hE0)
      have hb:=hp D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hDparent hE
      have hbound : outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
          Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=hb (by
        intro side neg Ψ' m' labels' X' F' K' hs hr' s
        have hrchild : fixedDepthRank Z K'≤r:=by omega
        have hDchild : Real.exp (radiusIter (2*A+11) r)*Z^3≤D:=by
          simpa only [radiusIter_succ] using hD
        have hh:=(hchildC side neg).2 D Z Ψ' m' labels' X' F' K' s hs hZ hZbig hfixed hrchild hDchild
        apply hh.trans
        rw [Real.norm_eq_abs]
        change childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2*(1+|s|)^dc≤_
        have hcscale : childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2≤
            (E0*Z^(57*η*(r:ℝ)))*(X'*F')^2:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcE side neg) (Real.rpow_nonneg hZ0.le _)) (sq_nonneg _)
        have hheight' : (1+|s|)^dc≤(1+|s|)^(2*J):=
          pow_le_pow_right₀ (by linarith [abs_nonneg s]) hdchild
        exact mul_le_mul hcscale hheight' (by positivity) (by positivity))
      apply hbound.trans
      have hexp : Z^(57*η*(r:ℝ))*Z^(57*η)=Z^(57*η*((r+1:ℕ):ℝ)):=by
        rw [←Real.rpow_add hZ0]
        congr 1
        push_cast
        ring
      calc
        Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J)=
            (Cp*E0)*(Z^(57*η*(r:ℝ))*Z^(57*η))*(X*F)^2*(1+|t|)^(2*J):=by dsimp [E];ring
        _ = (Cp*E0)*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by rw [hexp]
        _ ≤ _:=by gcongr

def canonicalDescentPadding (ε : ℝ) : ℝ:=canonicalPadding ε 57/2

theorem canonicalDescentPadding_budget (ε : ℝ) (hε : 0<ε) :
    0<canonicalDescentPadding ε ∧ canonicalDescentPadding ε≤(1:ℝ)/1000 ∧
    3000*canonicalDescentPadding ε≤(1:ℝ)/80 ∧
    171000*canonicalDescentPadding ε≤ε := by
  have h:=canonicalPadding_budget ε 57 hε (by norm_num)
  dsimp [canonicalDescentPadding]
  refine ⟨by linarith [h.1],by linarith [h.2.1],by linarith [h.2.2.1],?_⟩
  have ht:=h.2.2.2.2.1
  nlinarith [h.1]


end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open SchwartzPlanePoisson.CanonicalQuadraticSieve CanonicalCubeSeparation JointLogSeparation
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Bounded rank gives arbitrary small-power growth for the actual logarithmic energy. -/
theorem outsideLogEnergy_state_small_power
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (ε η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (hloss : 171000*η≤ε)
    (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→ |s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖ringComplex (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  obtain ⟨d,hd⟩:=outsideLogEnergy_finite_rank S hSp hbad base hbase Qbase h4 c hc hspan hsupport hperiod η hη hηsmall hbudget 3000 A hA
  refine ⟨d,?_⟩
  intro V hVs hV
  obtain ⟨C,hC,hbound⟩:=hd V hVs hV
  refine ⟨C,hC,?_⟩
  intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hD
  have hr:=fixedDepthRank_initial Z K hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global
  have hb:=hbound D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
  have he : 57*η*(3000:ℝ)≤ε:=by linarith
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le he) (zero_le_one.trans hC)

theorem outsideLogEnergy_small_power
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→ |s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : O→*ℂ) (m : O)
      (labels : Finset (Ideal O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z (canonicalDescentPadding ε) Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖ringComplex (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  have h:=canonicalDescentPadding_budget ε hε
  exact outsideLogEnergy_state_small_power S hSp hbad base hbase Qbase h4 c hc hspan hsupport hperiod
    ε (canonicalDescentPadding ε) h.1 h.2.1 h.2.2.1 h.2.2.2 A hA

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration
open TruncatedPrincipalPoisson MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- The actual initial prime-product rows have arbitrarily small-power density energy. -/
theorem outsideCanonicalDensity_small_power
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V₁ V₂ : ℝ→ℂ),ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
    ∃C Z₀ : ℝ,0<C ∧ 1≤Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ₁ Ψ₂ : O→*ℂ)
      (R : Finset (primePool (outsideSquarefreeIdeals S D)))
      (T : Finset (Ideal O×O)) (X F K : ℝ),
      Z₀≤Z → Real.exp (radiusIter A 3000)*Z^3≤D →
      IsBaseRayTwist base Ψ₁ → IsBaseRayTwist base Ψ₂ →
      0<X → 1≤F → 1≤K → X*F≤Z^2 →
      K*primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) R≤X*F*Z^(-(1:ℝ)/20) →
      (∀z∈T,z.1≠0 ∧ Squarefree z.1 ∧ IsCoprime z.1 (∏P∈S,P) ∧
        (Ideal.absNorm z.1:ℝ)≤F ∧ z.2≠0 ∧ ‖ringComplex z.2‖^2≤K) →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      densityChildEnergy (poolPrimary P) (poolPrimary_good P hP) (fun _=>1) (fun _=>1)
        Finset.univ Ψ₁ Ψ₂ (primeSubsetGenerator (fun i=>Ideal.span {poolPrimary P i}) R)
        T V₁ V₂ X X (2*d)≤C*Z^ε*(X*F)^2 := by
  obtain ⟨d,hd⟩:=outsideLogEnergy_small_power S hSp hbad base hbase Qbase h4 c hc hspan
    hsupport hperiod ε hε A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hV₁ hV₂ hs₁ hs₂
  have hleftSmooth : ContDiff ℝ ∞ (orientedLogProfile true V₁):=
    Complex.conjCLE.contDiff.comp hV₁
  have hleftSupport : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hs₁ s
    intro hz
    exact hs (by simp only [orientedLogProfile,ite_true,hz,star_zero])
  obtain ⟨C₁,hC₁,he₁⟩:=hd (orientedLogProfile true V₁) hleftSmooth hleftSupport
  obtain ⟨C₂,hC₂,he₂⟩:=hd (orientedLogProfile false V₂) hV₂ hs₂
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>firstLogDensity_nonneg 0 t)
  let C:=(Fintype.card Oˣ:ℝ)*(C₁+C₂)*I₀^3+1
  have hC : 0<C:=by dsimp only [C]; positivity
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro D Z Ψ₁ Ψ₂ R T X F K hlarge hD hΨ₁ hΨ₂ hX hF hK hmass hinv hT
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  let hg:=poolPrimary_good P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  let m:=primeSubsetGenerator (fun i=>Ideal.span {p i}) R
  let labels:=T.image Prod.fst
  obtain ⟨hZ,hZbig,hfixed⟩:=hthreshold Z hlarge
  have hη : 0≤canonicalDescentPadding ε:=(canonicalDescentPadding_budget ε hε).1.le
  have hlab : ∀z∈T,z.1≠0 ∧ Squarefree z.1 ∧ IsCoprime z.1 (∏P∈S,P) ∧ (Ideal.absNorm z.1:ℝ)≤F:=
    fun z hz=>⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.1⟩
  have hstate₁:=initialCanonicalState p hp (∏P∈S,P) base Ψ₁ hΨ₁
    Z (canonicalDescentPadding ε) X F K hZ.le hη hX hF hK R T hmass hinv hlab
  have hstate₂:=initialCanonicalState p hp (∏P∈S,P) base Ψ₂ hΨ₂
    Z (canonicalDescentPadding ε) X F K hZ.le hη hX hF hK R T hmass hinv hlab
  have hleft (t : ℝ) : canonicalLogEnergy p hg (fun _=>1) Finset.univ (normHeightTwist Ψ₁ t)
      m labels (orientedLogProfile true V₁) X K≤((C₁+C₂)*Z^ε)*(X*F)^2*(1+‖t‖)^(2*d) := by
    have hh:=he₁ D Z Ψ₁ m labels X F K t hstate₁ hZ hZbig hfixed hD
    change canonicalLogEnergy p hg (fun _=>1) Finset.univ (normHeightTwist Ψ₁ t)
      m labels (orientedLogProfile true V₁) X K≤_ at hh
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
    · linarith
    · linarith [abs_nonneg t]
    · omega
  have hright (t : ℝ) : canonicalLogEnergy p hg (fun _=>1) Finset.univ (normHeightTwist Ψ₂ t)
      m labels (orientedLogProfile false V₂) X K≤((C₁+C₂)*Z^ε)*(X*F)^2*(1+‖t‖)^(2*d) := by
    have hh:=he₂ D Z Ψ₂ m labels X F K t hstate₂ hZ hZbig hfixed hD
    change canonicalLogEnergy p hg (fun _=>1) Finset.univ (normHeightTwist Ψ₂ t)
      m labels (orientedLogProfile false V₂) X K≤_ at hh
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
    · linarith
    · linarith [abs_nonneg t]
    · omega
  have hb:=densityChildEnergy_from_canonical_heights p hp hg (fun _=>1) (fun _=>1)
    Finset.univ Ψ₁ Ψ₂ m T labels V₁ V₂ X F K ((C₁+C₂)*Z^ε) d hX
    (zero_lt_one.trans_le hK) (by positivity)
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    (fun z hz=>(hT z hz).2.2.2.2.2) (fun z hz=>(hT z hz).2.2.2.2.1) hleft hright
  apply hb.trans
  have hcoef : (Fintype.card Oˣ:ℝ)*(C₁+C₂)*I₀^3≤C:=by dsimp only [C]; linarith
  have he:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (zero_le_one.trans hZ.le) ε)) (sq_nonneg (X*F))
  convert he using 1 <;> ring

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson CompletedGauss SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass CanonicalCubeSeparation JointLogSeparation SecondPassIntegration
open TruncatedPrincipalPoisson MeasureTheory RayFourExpansion
open scoped BigOperators Classical SchwartzMap ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- The initial density estimate holds uniformly for both fixed residue phases and every nonzero mask. -/
theorem outsideCanonicalDensity_fixed_residues_small_power
    (S : Finset (Ideal O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (Qbase : Ideal O) (h4 : Qbase≤Ideal.span {(4:O)})
    (c : O) (hc : c≠0) (hspan : Ideal.span {c}=Qbase*Ideal.span {(72:O)})
    (hsupport : primeSupport (Ideal.span {c})⊆S)
    [Fintype (O⧸Ideal.span {9*c})]
    (hperiod : ∀x y : O,x-y∈Qbase → base x=base y)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V₁ V₂ : ℝ→ℂ),ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
    ∃C Z₀ : ℝ,0<C ∧ 1≤Z₀ ∧ ∀(D : ℕ) (Z : ℝ) (Ψ₁ Ψ₂ : O→*ℂ)
      (m : O) (negative₁ negative₂ : Bool) (r₁ s₁ r₂ s₂ : QuadraticRayRing)
      (T : Finset (Ideal O×O)) (X F K : ℝ),
      Z₀≤Z → Real.exp (radiusIter A 3000)*Z^3≤D →
      IsBaseRayTwist base Ψ₁ → IsBaseRayTwist base Ψ₂ → m≠0 →
      0<X → 1≤F → 1≤K → X*F≤Z^2 →
      K*‖ringComplex m‖^2≤X*F*Z^(-(1:ℝ)/20) →
      (∀z∈T,z.1≠0 ∧ Squarefree z.1 ∧ IsCoprime z.1 (∏P∈S,P) ∧
        (Ideal.absNorm z.1:ℝ)≤F ∧ z.2≠0 ∧ ‖ringComplex z.2‖^2≤K) →
      let P:=outsideSquarefreeIdeals S D
      let hP:=outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span P hP i]; infer_instance
      densityChildEnergy (poolPrimary P) (poolPrimary_good P hP)
        (combinedFixedColumn (poolPrimary P) (poolPrimary_good P hP) negative₁ r₁ s₁ (fun _=>1))
        (combinedFixedColumn (poolPrimary P) (poolPrimary_good P hP) negative₂ r₂ s₂ (fun _=>1))
        Finset.univ Ψ₁ Ψ₂ m
        T V₁ V₂ X X (2*d)≤C*Z^ε*(X*F)^2 := by
  obtain ⟨d,hd⟩:=outsideLogEnergy_small_power S hSp hbad base hbase Qbase h4 c hc hspan
    hsupport hperiod ε hε A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hV₁ hV₂ hs₁ hs₂
  have hleftSmooth : ContDiff ℝ ∞ (orientedLogProfile true V₁):=
    Complex.conjCLE.contDiff.comp hV₁
  have hleftSupport : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hs₁ s
    intro hz
    exact hs (by simp only [orientedLogProfile,ite_true,hz,star_zero])
  obtain ⟨C₁,hC₁,he₁⟩:=hd (orientedLogProfile true V₁) hleftSmooth hleftSupport
  obtain ⟨C₂,hC₂,he₂⟩:=hd (orientedLogProfile false V₂) hV₂ hs₂
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>firstLogDensity_nonneg 0 t)
  let C:=(Fintype.card Oˣ:ℝ)*(C₁+C₂)*I₀^3+1
  have hC : 0<C:=by dsimp only [C]; positivity
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro D Z Ψ₁ Ψ₂ m negative₁ negative₂ r₁ s₁ r₂ s₂ T X F K hlarge hD hΨ₁ hΨ₂ hm hX hF hK hmass hinv hT
  let P:=outsideSquarefreeIdeals S D
  let hP:=outsideSquarefree_admissible S D hbad
  let p:=poolPrimary P
  let hp:=poolPrimary_ne_zero P hP
  let hg:=poolPrimary_good P hP
  letI : ∀i : primePool P,(Ideal.span {p i}).IsMaximal:=
    fun i=>by change (Ideal.span {poolPrimary P i}).IsMaximal; rw [poolPrimary_span P hP i]; infer_instance
  let labels:=T.image Prod.fst
  obtain ⟨hZ,hZbig,hfixed⟩:=hthreshold Z hlarge
  have hη : 0≤canonicalDescentPadding ε:=(canonicalDescentPadding_budget ε hε).1.le
  have hlab : ∀z∈T,z.1≠0 ∧ Squarefree z.1 ∧ IsCoprime z.1 (∏P∈S,P) ∧ (Ideal.absNorm z.1:ℝ)≤F:=
    fun z hz=>⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.1⟩
  have hstate₁ (χ : RayCharacter):=initialCanonicalState_mask (∏P∈S,P) base
    (Ψ₁*rayMonoid χ) (hΨ₁.mul_ray_right χ) m hm
    Z (canonicalDescentPadding ε) X F K hZ.le hη hX hF hK T hmass hinv hlab
  have hstate₂ (χ : RayCharacter):=initialCanonicalState_mask (∏P∈S,P) base
    (Ψ₂*rayMonoid χ) (hΨ₂.mul_ray_right χ) m hm
    Z (canonicalDescentPadding ε) X F K hZ.le hη hX hF hK T hmass hinv hlab
  have hleft (t : ℝ) : canonicalLogEnergy p hg (combinedFixedColumn p hg negative₁ r₁ s₁ (fun _=>1)) Finset.univ (normHeightTwist Ψ₁ t)
      m labels (orientedLogProfile true V₁) X K≤((C₁+C₂)*Z^ε)*(X*F)^2*(1+‖t‖)^(2*d) := by
    apply canonicalLogEnergy_combined_uniform p hg (poolPrimary_odd P hP) Finset.univ
      (normHeightTwist Ψ₁ t) m labels negative₁ r₁ s₁ (fun _=>1) _ X K _
      (zero_lt_one.trans_le hK) (by positivity)
    intro χ
    rw [←normHeightTwist_mul]
    have hh:=he₁ D Z (Ψ₁*rayMonoid χ) m labels X F K t (hstate₁ χ) hZ hZbig hfixed hD
    change canonicalLogEnergy p hg (fun _=>1) Finset.univ (normHeightTwist (Ψ₁*rayMonoid χ) t)
      m labels (orientedLogProfile true V₁) X K≤_ at hh
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
    · linarith
    · linarith [abs_nonneg t]
    · omega
  have hright (t : ℝ) : canonicalLogEnergy p hg (combinedFixedColumn p hg negative₂ r₂ s₂ (fun _=>1)) Finset.univ (normHeightTwist Ψ₂ t)
      m labels (orientedLogProfile false V₂) X K≤((C₁+C₂)*Z^ε)*(X*F)^2*(1+‖t‖)^(2*d) := by
    apply canonicalLogEnergy_combined_uniform p hg (poolPrimary_odd P hP) Finset.univ
      (normHeightTwist Ψ₂ t) m labels negative₂ r₂ s₂ (fun _=>1) _ X K _
      (zero_lt_one.trans_le hK) (by positivity)
    intro χ
    rw [←normHeightTwist_mul]
    have hh:=he₂ D Z (Ψ₂*rayMonoid χ) m labels X F K t (hstate₂ χ) hZ hZbig hfixed hD
    change canonicalLogEnergy p hg (fun _=>1) Finset.univ (normHeightTwist (Ψ₂*rayMonoid χ) t)
      m labels (orientedLogProfile false V₂) X K≤_ at hh
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
    · linarith
    · linarith [abs_nonneg t]
    · omega
  have hb:=densityChildEnergy_from_canonical_heights p hp hg
    (combinedFixedColumn p hg negative₁ r₁ s₁ (fun _=>1))
    (combinedFixedColumn p hg negative₂ r₂ s₂ (fun _=>1))
    Finset.univ Ψ₁ Ψ₂ m T labels V₁ V₂ X F K ((C₁+C₂)*Z^ε) d hX
    (zero_lt_one.trans_le hK) (by positivity)
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    (fun z hz=>(hT z hz).2.2.2.2.2) (fun z hz=>(hT z hz).2.2.2.2.1) hleft hright
  apply hb.trans
  have hcoef : (Fintype.card Oˣ:ℝ)*(C₁+C₂)*I₀^3≤C:=by dsimp only [C]; linarith
  have he:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (zero_le_one.trans hZ.le) ε)) (sq_nonneg (X*F))
  convert he using 1 <;> ring

end CanonicalRowCompletion

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
def fixedCuspArrayWithPhase (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  phaseArray m n b*fixedConjugateCuspArray cusp u m n b

lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)

lemma fixedCuspArrayWithPhase_zero (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible n b) : fixedCuspArrayWithPhase cusp u phaseArray m n b=0 := by
  simp only [fixedCuspArrayWithPhase,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero,mul_zero]

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein
open scoped BigOperators Classical MatrixGroups
local notation "Eis" => Eisenstein.O

lemma cuspBadModulus_ne_zero (c:Eis) (hc:c≠0) : traceLambda^3*c≠0 :=
  mul_ne_zero (pow_ne_zero _ traceLambda_ne_zero) hc

def cuspBadPhase (c:Eis) (hc:c≠0) (d U x:Eis) : ℂ :=
  residueTraceQuotientChar 1 (traceLambda^3*c) (cuspBadModulus_ne_zero c hc)
    (Ideal.Quotient.mk _ (-d*U*x))

lemma cuspBadPhase_eq (c:Eis) (hc:c≠0) (d U x:Eis) :
    cuspBadPhase c hc d U x =
      tracePhase (-(ringComplex d*ringComplex U*(ringComplex x/(ringComplex traceLambda)^4))/ringComplex c) := by
  rw [cuspBadPhase,residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [one_mul,map_mul,map_pow,map_neg,map_ofNat,map_one]
  congr 1
  field_simp [ringComplex_ne_zero traceLambda_ne_zero,ringComplex_ne_zero hc] <;> ring

lemma cuspBadPhase_eq_of_residue (c:Eis) (hc:c≠0) (d U d' U' x:Eis)
    (hres:traceLambda^3*c∣d*U-d'*U') :
    cuspBadPhase c hc d U x=cuspBadPhase c hc d' U' x := by
  unfold cuspBadPhase
  congr 1
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd:=dvd_mul_of_dvd_left hres (-x)
  convert hd using 1 <;> ring

lemma cuspBadPhase_norm (c:Eis) (hc:c≠0) (d U x:Eis) :
    ‖cuspBadPhase c hc d U x‖=1 := by
  rw [cuspBadPhase_eq]
  exact tracePhase_norm _

def cuspResiduePhase (c:Eis) (hc:c≠0)
    (v:Eis⧸Ideal.span {traceLambda^3*c}) (x:Eis) : ℂ :=
  residueTraceQuotientChar 1 (traceLambda^3*c) (cuspBadModulus_ne_zero c hc)
    (v*Ideal.Quotient.mk _ x)

lemma cuspBadPhase_as_fixed_residue (c:Eis) (hc:c≠0) (d U:Eis) :
    cuspBadPhase c hc d U=cuspResiduePhase c hc (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [cuspBadPhase,cuspResiduePhase,map_mul]

lemma cuspResiduePhase_norm (c:Eis) (hc:c≠0)
    (v:Eis⧸Ideal.span {traceLambda^3*c}) (x:Eis) : ‖cuspResiduePhase c hc v x‖=1 := by
  let : Finite (Eis⧸Ideal.span {traceLambda^3*c}) :=
    (Ideal.span {traceLambda^3*c}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (cuspBadModulus_ne_zero c hc))
  exact AddChar.norm_apply _ _

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
theorem cuspMatrix_character_frequency_sum {ι : Type*} [Fintype ι] (p t : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (ht : ∀ i, p i ∣ cuspPrimeCofactor p i * t i - 1)
    (c U w x : O) (hc : c ≠ 0)
    (hbez : U * (∏ i, p i) + (traceLambda ^ 3 * w) * c = 1)
    (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O))
    (hM : ∀ v, (∏ i, p i) ∣ M v 1 0)
    (hfixed : ∀ v, traceLambda ^ 3 * c ∣ M v 1 1 - M (fun _ => 1) 1 1)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (hfreq : ∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (M v 0 0) =
      (σ i : O ⧸ Ideal.span {p i}) * (v i : O ⧸ Ideal.span {p i}))
    (hε : ∀ i, Ideal.Quotient.mk (Ideal.span {p i})
      (traceLambda ^ 3 * c * cuspPrimeCofactor p i) *
      (σ i : O ⧸ Ideal.span {p i}) * (ε i : O ⧸ Ideal.span {p i}) = -1)
    (κ : ℂ) (χ₀ : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → ℂ) (hκ : ∀ v, χ₀ v =
      κ * ringComplex (symbol (M v 0 0) (∏ i, p i))) (j : ι → ℕ) :
    (∑ v : ∀ i, (O ⧸ Ideal.span {p i})ˣ,
      (∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i))
        (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ)
        (v i : O ⧸ Ideal.span {p i})) *
      star (χ₀ v) *
      tracePhase (-(ringComplex (M v 1 1) * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c * ringComplex (∏ i, p i)))) =
    (star κ * tracePhase (-(ringComplex (M (fun _ => 1) 1 1) * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c))) *
      ∏ i, ((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹ ^ 2) (σ i) *
        ((Fintype.card (O ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
          gaussSum (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)
            ((residueTraceQuotientChar 1 (p i) (hp i)).mulShift (-1)) *
          gaussSum (complexSexticChar (Ideal.span {p i}) (hg i) ^ (j i + 2))
            ((residueTraceQuotientChar 1 (p i) (hp i)).mulShift
              ((ε i : O ⧸ Ideal.span {p i}) * Ideal.Quotient.mk (Ideal.span {p i}) x))) := by
  classical
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let ψ := fun i => residueTraceQuotientChar 1 (p i) (hp i)
  let C := star κ * tracePhase
    (-(ringComplex (M (fun _ => 1) 1 1) * ringComplex U * ringComplex x) /
      (ringComplex traceLambda ^ 4 * ringComplex c))
  let f := fun (i : ι) (v : (O ⧸ Ideal.span {p i})ˣ) =>
    finiteAdditiveFourierCoeff (ψ i) (χ i ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ) v *
      ((χ i)⁻¹ ^ 2) v * ψ i ((ε i : O ⧸ Ideal.span {p i}) *
        Ideal.Quotient.mk (Ideal.span {p i}) x * (↑v⁻¹ : O ⧸ Ideal.span {p i}))
  have hpoint (v : ∀ i, (O ⧸ Ideal.span {p i})ˣ) :
      (∏ i, finiteAdditiveFourierCoeff (ψ i) (χ i ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ) (v i)) *
      star (χ₀ v) *
      tracePhase (-(ringComplex (M v 1 1) * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c * ringComplex (∏ i, p i))) =
      (C * ∏ i, ((χ i)⁻¹ ^ 2) (σ i)) * ∏ i, f i (v i) := by
    rw [hκ v, star_mul, cuspSymbol_sextic_product p hg,
      cuspMatrix_inverse_phase_product p t hp hpair ht c U w x hc hbez (M v) (hM v) σ ε v (hfreq v) hε,
      cuspInverse_fixed_phase_congr c _ _ U x hc (hfixed v)]
    simp_rw [hfreq v]
    simp only [map_mul, Finset.prod_mul_distrib, C, f, χ, ψ]
    ring
  calc
    _ = (C * ∏ i, ((χ i)⁻¹ ^ 2) (σ i)) * ∑ v : ∀ i, (O ⧸ Ideal.span {p i})ˣ, ∏ i, f i (v i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => hpoint v)
    _ = (C * ∏ i, ((χ i)⁻¹ ^ 2) (σ i)) * ∏ i, ∑ v : (O ⧸ Ideal.span {p i})ˣ, f i v := by
      rw [← Fintype.prod_sum f]
    _ = _ := by
      have he (i) : (∑ v : (O ⧸ Ideal.span {p i})ˣ, f i v) =
          (Fintype.card (O ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
          gaussSum (χ i ^ j i) ((ψ i).mulShift (-1)) *
          gaussSum (χ i ^ (j i + 2)) ((ψ i).mulShift
            ((ε i : O ⧸ Ideal.span {p i}) * Ideal.Quotient.mk (Ideal.span {p i}) x)) :=
        finiteReflectionGauss_product (χ i) (ψ i) (j i) _
      simp_rw [he]
      dsimp only [C, χ, ψ]
      simp only [Finset.prod_mul_distrib]
      ring



end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
