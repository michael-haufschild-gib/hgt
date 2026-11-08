import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedProbeAtoms
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionCompactness
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector
import GaloisForLFunctions.RHTower.ZetaFisherVariance
import Mathlib.Analysis.PSeries
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionPrimePairKernel
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation

/-!
# The sharp Hilbert–Schmidt boundary of the torsion operator

The normalized arithmetic matrix is the matrix of the actual compact torsion
operator. Its divisor half reindexes by a conductor and its positive integral
multiple. Parseval and nonnegative product summation give an exact square-mass
formula. The operator is Hilbert–Schmidt precisely above conductor weight
one half; even-conductor tame diagonals force the converse.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory ArithmeticCouplingTheory

/-- The actual torsion-limit matrix in normalized conductor coordinates. -/
def spacingNormalizedMatrix (δ : ℝ) (m n : ℕ) : ℝ :=
  ((m+1:ℕ):ℝ)^(-δ/2)*((n+1:ℕ):ℝ)^(-δ/2)*spacingLimitKernel (m+1) (n+1)

/-- The normalized arithmetic matrix is the Hilbert matrix of the actual limit operator. -/
theorem spacingNormalizedMatrix_inner (δ : ℝ) (hδ : 0 < δ) (m n : ℕ) :
    inner ℝ (weightedProbeBasis δ n)
      (spacingLimitHilbertOperator δ hδ (weightedProbeBasis δ m)) =
        spacingNormalizedMatrix δ m n := by
  rw [real_inner_comm,spacingLimitHilbertOperator_inner,
    weightedProbeBasis_apply,weightedProbeBasis_apply,weightedKernelPairing_normalizedAtoms]
  rfl

/-- Every normalized matrix row has square sum equal to the squared norm of its operator image. -/
theorem spacingNormalizedMatrix_row_parseval (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    (Summable fun n => (spacingNormalizedMatrix δ m n)^2) ∧
      (∑' n, (spacingNormalizedMatrix δ m n)^2) =
        ‖spacingLimitHilbertOperator δ hδ (weightedProbeBasis δ m)‖^2 := by
  have hs := (weightedProbeBasis δ).summable_norm_inner_sq
    (spacingLimitHilbertOperator δ hδ (weightedProbeBasis δ m))
  have ht := (weightedProbeBasis δ).tsum_norm_inner_sq
    (spacingLimitHilbertOperator δ hδ (weightedProbeBasis δ m))
  simp only [spacingNormalizedMatrix_inner,Real.norm_eq_abs,sq_abs] at hs ht
  exact ⟨hs,ht⟩

/-- Hilbert–Schmidt membership is exactly summability of the original normalized matrix squares. -/
theorem spacingLimitHilbertOperator_hilbertSchmidt_iff_matrix (δ : ℝ) (hδ : 0 < δ) :
    (spacingLimitHilbertOperator δ hδ).IsHilbertSchmidt ↔
      Summable (fun p : ℕ×ℕ => (spacingNormalizedMatrix δ p.1 p.2)^2) := by
  rw [ContinuousLinearMap.isHilbertSchmidt_iff_summable (weightedProbeBasis δ)]
  have hr := spacingNormalizedMatrix_row_parseval δ hδ
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro hs
    exact ⟨fun m => (hr m).1,hs.congr fun m => (hr m).2.symm⟩
  · intro hs
    exact hs.2.congr fun m => (hr m).2

/-- The Hilbert–Schmidt norm is the exact square mass of the original normalized matrix. -/
theorem spacingLimitHilbertOperator_hsNormSq_matrix (δ : ℝ) (hδ : 0 < δ)
    (hs : (spacingLimitHilbertOperator δ hδ).IsHilbertSchmidt) :
    ContinuousLinearMap.hsNormSq (spacingLimitHilbertOperator δ hδ) =
      ∑' p : ℕ×ℕ, (spacingNormalizedMatrix δ p.1 p.2)^2 := by
  rw [ContinuousLinearMap.hsNormSq_eq hs (weightedProbeBasis δ)]
  have hm := (spacingLimitHilbertOperator_hilbertSchmidt_iff_matrix δ hδ).mp hs
  calc _ = ∑' m : ℕ, ∑' n : ℕ, (spacingNormalizedMatrix δ m n)^2 :=
      tsum_congr (fun m => (spacingNormalizedMatrix_row_parseval δ hδ m).2.symm)
       _ = _ := hm.tsum_prod.symm

#print axioms spacingNormalizedMatrix_inner
#print axioms spacingNormalizedMatrix_row_parseval
#print axioms spacingLimitHilbertOperator_hilbertSchmidt_iff_matrix
#print axioms spacingLimitHilbertOperator_hsNormSq_matrix

open ArithmeticCouplingTheory

/-- The divisor half of the prime matrix in normalized conductor coordinates. -/
def spacingDivisorMatrix (δ : ℝ) (m n : ℕ) : ℝ :=
  ((m+1:ℕ):ℝ)^(-δ/2)*((n+1:ℕ):ℝ)^(-δ/2)*divisorKernel (m+1) (n+1)

/-- Positive divisor pairs, expressed in zero-based Hilbert coordinates. -/
def spacingDilationPair (p : ℕ×ℕ) : ℕ×ℕ :=
  (p.1,(p.1+1)*(p.2+1)-1)

theorem spacingDilationPair_injective : Function.Injective spacingDilationPair := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hac : a=c := congrArg Prod.fst h
  subst c
  have hs := congrArg Prod.snd h
  change (a+1)*(b+1)-1=(a+1)*(d+1)-1 at hs
  have hmul : (a+1)*(b+1)=(a+1)*(d+1) := by
    have hh:=congrArg (fun n : ℕ=>n+1) hs
    simpa only [Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b)),
      Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos d))] using hh
  have hbd := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos a) hmul
  exact Prod.ext rfl (by omega)

/-- A nonzero divisor entry lies in the unique dilation parametrization. -/
theorem spacingDivisorMatrix_zero_off_dilations (δ : ℝ) (p : ℕ×ℕ)
    (hp : p ∉ Set.range spacingDilationPair) : spacingDivisorMatrix δ p.1 p.2=0 := by
  have hnd : ¬p.1+1∣p.2+1 := by
    rintro ⟨t,ht⟩
    have ht0 : 0 < t := by
      by_contra h
      have hz : t=0 := by omega
      rw [hz,mul_zero] at ht
      omega
    apply hp
    refine ⟨(p.1,t-1),?_⟩
    apply Prod.ext
    · rfl
    · change (p.1+1)*(t-1+1)-1=p.2
      rw [Nat.sub_add_cancel ht0,←ht,Nat.add_sub_cancel]
  simp only [spacingDivisorMatrix,divisorKernel,if_neg hnd,mul_zero]

private theorem spacing_dilation_square (δ : ℝ) (m t : ℝ) (hm : 0 < m) (ht : 0 < t) (a : ℝ) :
    (m^(-δ/2)*(m*t)^(-δ/2)*(a/Real.sqrt t))^2 =
      m^(-2*δ)*(a^2*t^(-(1+δ))) := by
  have hw (x : ℝ) (hx : 0 < x) : (x^(-δ/2))^2=x^(-δ) := by
    rw [pow_two,←Real.rpow_add hx]
    congr 1
    ring
  rw [mul_pow,mul_pow,hw m hm,hw (m*t) (mul_pos hm ht),div_pow,Real.sq_sqrt ht.le,
    Real.mul_rpow hm.le ht.le]
  have hmexp : m^(-δ)*m^(-δ)=m^(-2*δ) := by
    rw [←Real.rpow_add hm]
    congr 1
    ring
  have htexp : t^(-δ)/t=t^(-(1+δ)) := by
    rw [show -(1+δ)=-δ-1 by ring,Real.rpow_sub ht,Real.rpow_one]
  calc _ = (m^(-δ)*m^(-δ))*(a^2*(t^(-δ)/t)) := by ring
       _ = _ := by rw [hmexp,htexp]

/-- The squared divisor matrix factors into a conductor power and a ratio power. -/
theorem spacingDivisorMatrix_dilation_square (δ : ℝ) (p : ℕ×ℕ) :
    (spacingDivisorMatrix δ (spacingDilationPair p).1 (spacingDilationPair p).2)^2 =
      ((p.1+1:ℕ):ℝ)^(-2*δ)*
        ((Λ (p.2+1):ℝ)^2*((p.2+1:ℕ):ℝ)^(-(1+δ))) := by
  have hm : 0 < p.1+1 := Nat.succ_pos _
  have ht : 0 < p.2+1 := Nat.succ_pos _
  simp only [spacingDivisorMatrix,spacingDilationPair,Nat.sub_add_cancel (Nat.mul_pos hm ht),
    divisorKernel,if_pos (dvd_mul_right (p.1+1) (p.2+1)),
    Nat.mul_div_cancel_left _ hm,Nat.cast_mul]
  exact spacing_dilation_square δ ((p.1+1:ℕ):ℝ) ((p.2+1:ℕ):ℝ) (by positivity) (by positivity) _

/-- The ratio energy converges at every positive conductor exponent. -/
theorem spacing_ratio_square_summable (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun t : ℕ => (Λ (t+1):ℝ)^2*((t+1:ℕ):ℝ)^(-(1+δ))) := by
  have hlog := RHTower.summable_log_natCast_pow_mul_rpow_neg 2 (by linarith : 1<1+δ)
  have hs := hlog.comp_injective Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  have hl : (Λ (n+1):ℝ)≤Real.log ((n+1:ℕ):ℝ) := ArithmeticFunction.vonMangoldt_le_log
  exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg hl 2

/-- Above the square-summability boundary, the entire divisor matrix has finite square mass. -/
theorem spacingDivisorMatrix_square_summable (δ : ℝ) (hδ : 1/2 < δ) :
    Summable (fun p : ℕ×ℕ => (spacingDivisorMatrix δ p.1 p.2)^2) := by
  have hm : Summable (fun n : ℕ=>((n+1:ℕ):ℝ)^(-2*δ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -2*δ < -1)).comp_injective Nat.succ_injective
  have ht := spacing_ratio_square_summable δ (by linarith)
  have hprod : Summable (fun p : ℕ×ℕ => ((p.1+1:ℕ):ℝ)^(-2*δ)*
      ((Λ (p.2+1):ℝ)^2*((p.2+1:ℕ):ℝ)^(-(1+δ)))) := by
    apply (summable_prod_of_nonneg (f := fun p : ℕ×ℕ=>
      ((p.1+1:ℕ):ℝ)^(-2*δ)*((Λ (p.2+1):ℝ)^2*((p.2+1:ℕ):ℝ)^(-(1+δ))))
      (fun p=>mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)))).mpr
    refine ⟨fun n => ht.mul_left (((n+1:ℕ):ℝ)^(-2*δ)),?_⟩
    simpa only [tsum_mul_left] using hm.mul_right
      (∑' t : ℕ, (Λ (t+1):ℝ)^2*((t+1:ℕ):ℝ)^(-(1+δ)))
  apply (spacingDilationPair_injective.summable_iff (fun p hp => by
    rw [spacingDivisorMatrix_zero_off_dilations δ p hp,zero_pow (by decide : 2≠0)])).mp
  exact hprod.congr fun p => (spacingDivisorMatrix_dilation_square δ p).symm

/-- The divisor square mass factors exactly into conductor and prime-ratio Dirichlet sums. -/
theorem spacingDivisorMatrix_square_tsum (δ : ℝ) (hδ : 1/2 < δ) :
    (∑' p : ℕ×ℕ, (spacingDivisorMatrix δ p.1 p.2)^2) =
      (∑' m : ℕ, ((m+1:ℕ):ℝ)^(-2*δ))*
        (∑' t : ℕ, (Λ (t+1):ℝ)^2*((t+1:ℕ):ℝ)^(-(1+δ))) := by
  have hs := spacingDivisorMatrix_square_summable δ hδ
  have hprod := (hs.comp_injective spacingDilationPair_injective).congr
    (fun p => spacingDivisorMatrix_dilation_square δ p)
  have hm : Summable (fun n : ℕ=>((n+1:ℕ):ℝ)^(-2*δ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -2*δ < -1)).comp_injective Nat.succ_injective
  have ht := spacing_ratio_square_summable δ (by linarith)
  have hsupport : Function.support (fun p : ℕ×ℕ => (spacingDivisorMatrix δ p.1 p.2)^2) ⊆
      Set.range spacingDilationPair := by
    intro p hp
    by_contra h
    apply hp
    change (spacingDivisorMatrix δ p.1 p.2)^2=0
    rw [spacingDivisorMatrix_zero_off_dilations δ p h,zero_pow (by decide : 2≠0)]
  calc _ = ∑' p : ℕ×ℕ,
        (spacingDivisorMatrix δ (spacingDilationPair p).1 (spacingDilationPair p).2)^2 :=
      (spacingDilationPair_injective.tsum_eq hsupport).symm
       _ = ∑' p : ℕ×ℕ, ((p.1+1:ℕ):ℝ)^(-2*δ)*
        ((Λ (p.2+1):ℝ)^2*((p.2+1:ℕ):ℝ)^(-(1+δ))) :=
      tsum_congr (spacingDivisorMatrix_dilation_square δ)
       _ = _ := (hm.tsum_mul_tsum ht hprod).symm

#print axioms spacingDilationPair_injective
#print axioms spacingDivisorMatrix_dilation_square
#print axioms spacing_ratio_square_summable
#print axioms spacingDivisorMatrix_square_summable
#print axioms spacingDivisorMatrix_square_tsum

open ArithmeticEffectivityTheory ArithmeticIntersectionTheory ArithmeticCouplingTheory

/-- The squared normalized tame diagonal. -/
def spacingDiagonalSquare (δ : ℝ) (n : ℕ) : ℝ :=
  ((n+1:ℕ):ℝ)^(-2*δ)*(tameDifferent (n+1))^2

/-- The normalized diagonal is the tame different times the conductor power. -/
theorem spacingNormalizedMatrix_self (δ : ℝ) (n : ℕ) :
    spacingNormalizedMatrix δ n n = ((n+1:ℕ):ℝ)^(-δ)*tameDifferent (n+1) := by
  rw [spacingNormalizedMatrix,spacingLimitKernel_self,
    ←Real.rpow_add (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity),
    show -δ/2 + -δ/2 = -δ by ring]

/-- Squaring the actual diagonal gives its exact normalized tame square. -/
theorem spacingNormalizedMatrix_self_sq (δ : ℝ) (n : ℕ) :
    (spacingNormalizedMatrix δ n n)^2=spacingDiagonalSquare δ n := by
  rw [spacingNormalizedMatrix_self,mul_pow]
  unfold spacingDiagonalSquare
  congr 1
  rw [pow_two,←Real.rpow_add (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)]
  congr 1
  ring

private theorem spacing_divisor_self (n : ℕ) : divisorKernel (n+1) (n+1)=0 := by
  rw [divisorKernel,if_pos (dvd_refl _),Nat.div_self (Nat.succ_pos _),
    ArithmeticFunction.vonMangoldt_apply_one,zero_div]

/-- Matrix square mass splits exactly into the two divisor orientations and the tame diagonal. -/
theorem spacingNormalizedMatrix_square_split (δ : ℝ) (m n : ℕ) :
    (spacingNormalizedMatrix δ m n)^2 =
      (spacingDivisorMatrix δ m n)^2+(spacingDivisorMatrix δ n m)^2+
        if m=n then spacingDiagonalSquare δ n else 0 := by
  by_cases h : m=n
  · subst n
    have hm : (0:ℝ)<((m+1:ℕ):ℝ) := by positivity
    have hw : (((m+1:ℕ):ℝ)^(-δ/2)*((m+1:ℕ):ℝ)^(-δ/2))^2 =
        ((m+1:ℕ):ℝ)^(-2*δ) := by
      rw [←Real.rpow_add hm,pow_two,←Real.rpow_add hm]
      congr 1
      ring
    rw [spacingNormalizedMatrix,spacingLimitKernel_self]
    simp only [spacingDivisorMatrix,spacing_divisor_self,mul_zero,
      zero_pow (by decide : 2≠0),zero_add,ite_true,spacingDiagonalSquare]
    rw [mul_pow,hw]
  · have hnat : m+1≠n+1 := by omega
    have hz : divisorKernel (m+1) (n+1)*divisorKernel (n+1) (m+1)=0 := by
      by_cases hd : m+1∣n+1
      · have hnd : ¬n+1∣m+1 := fun hnd => hnat (Nat.dvd_antisymm hd hnd)
        simp only [divisorKernel,if_pos hd,if_neg hnd,mul_zero]
      · simp only [divisorKernel,if_neg hd,zero_mul]
    have hc : spacingDivisorMatrix δ m n*spacingDivisorMatrix δ n m=0 := by
      calc
        spacingDivisorMatrix δ m n*spacingDivisorMatrix δ n m =
            (((m+1:ℕ):ℝ)^(-δ/2))^2*(((n+1:ℕ):ℝ)^(-δ/2))^2*
              (divisorKernel (m+1) (n+1)*divisorKernel (n+1) (m+1)) := by
          unfold spacingDivisorMatrix
          ring
        _ = 0 := by rw [hz,mul_zero]
    have he : spacingNormalizedMatrix δ m n =
        -spacingDivisorMatrix δ m n-spacingDivisorMatrix δ n m := by
      rw [spacingNormalizedMatrix,spacingLimitKernel,if_neg hnat,add_zero,
        weilPrimeKernel_eq_divisorKernel_add]
      unfold spacingDivisorMatrix
      ring
    rw [if_neg h,add_zero,he]
    nlinarith only [hc]

/-- The tame diagonal has finite square mass above the conductor boundary. -/
theorem spacingDiagonalSquare_summable (δ : ℝ) (hδ : 1/2 < δ) :
    Summable (spacingDiagonalSquare δ) := by
  have hs := (RHTower.summable_log_natCast_pow_mul_rpow_neg 2 (by linarith : 1<2*δ)).comp_injective
    Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun n => by unfold spacingDiagonalSquare; positivity)
    (fun n => ?_) hs
  have hd := RenormalizedArithmeticPotentialTheory.tameDifferent_le_log (Nat.succ_pos n)
  have hd0 := RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg (n+1)
  calc spacingDiagonalSquare δ n ≤
        ((n+1:ℕ):ℝ)^(-2*δ)*(Real.log ((n+1:ℕ):ℝ))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hd 2) (Real.rpow_nonneg (by positivity) _)
       _ = (Real.log ((n+1:ℕ):ℝ))^2*((n+1:ℕ):ℝ)^(-(2*δ)) := by
        rw [show -(2*δ) = -2*δ by ring]
        exact mul_comm _ _

/-- Embedding the tame square sequence on the matrix diagonal preserves summability. -/
theorem spacingDiagonalMatrix_square_summable (δ : ℝ) (hδ : 1/2 < δ) :
    Summable (fun p : ℕ×ℕ => if p.1=p.2 then spacingDiagonalSquare δ p.2 else 0) := by
  have hinj : Function.Injective (fun n : ℕ => (n,n)) := fun _ _ h => congrArg Prod.fst h
  have hz (p : ℕ×ℕ) (hp : p∉Set.range (fun n : ℕ => (n,n))) :
      (if p.1=p.2 then spacingDiagonalSquare δ p.2 else 0)=0 := by
    have hne : p.1≠p.2 := by
      intro he
      apply hp
      exact ⟨p.1,Prod.ext rfl he⟩
    exact if_neg hne
  apply (hinj.summable_iff hz).mp
  exact (spacingDiagonalSquare_summable δ hδ).congr fun n => by
    simp only [Function.comp_apply,ite_true]

/-- The actual normalized torsion matrix is square-summable above one half. -/
theorem spacingNormalizedMatrix_square_summable (δ : ℝ) (hδ : 1/2 < δ) :
    Summable (fun p : ℕ×ℕ => (spacingNormalizedMatrix δ p.1 p.2)^2) := by
  have hd := spacingDivisorMatrix_square_summable δ hδ
  have ht : Summable (fun p : ℕ×ℕ=>(spacingDivisorMatrix δ p.2 p.1)^2) :=
    hd.comp_injective (i := fun p : ℕ×ℕ => (p.2,p.1))
      (Equiv.prodComm ℕ ℕ).injective
  have hdiag := spacingDiagonalMatrix_square_summable δ hδ
  exact ((hd.add ht).add hdiag).congr fun p =>
    (spacingNormalizedMatrix_square_split δ p.1 p.2).symm

/-- The matrix diagonal sum is exactly its conductor square sum. -/
theorem spacingDiagonalMatrix_square_tsum (δ : ℝ) :
    (∑' p : ℕ×ℕ, if p.1=p.2 then spacingDiagonalSquare δ p.2 else 0) =
      ∑' n : ℕ, spacingDiagonalSquare δ n := by
  have hinj : Function.Injective (fun n : ℕ => (n,n)) := fun _ _ h => congrArg Prod.fst h
  have hsupp : Function.support
      (fun p : ℕ×ℕ => if p.1=p.2 then spacingDiagonalSquare δ p.2 else 0) ⊆
        Set.range (fun n : ℕ => (n,n)) := by
    intro p hp
    by_cases h : p.1=p.2
    · exact ⟨p.1,Prod.ext rfl h⟩
    · exact (hp (if_neg h)).elim
  simpa only [ite_true] using (hinj.tsum_eq hsupp).symm

/-- The actual normalized square mass has an exact divisor-series and tame-diagonal decomposition. -/
theorem spacingNormalizedMatrix_square_tsum (δ : ℝ) (hδ : 1/2 < δ) :
    (∑' p : ℕ×ℕ, (spacingNormalizedMatrix δ p.1 p.2)^2) =
      2*(∑' m : ℕ, ((m+1:ℕ):ℝ)^(-2*δ))*
        (∑' t : ℕ, (Λ (t+1):ℝ)^2*((t+1:ℕ):ℝ)^(-(1+δ)))+
      ∑' n : ℕ, spacingDiagonalSquare δ n := by
  have hd := spacingDivisorMatrix_square_summable δ hδ
  have ht : Summable (fun p : ℕ×ℕ=>(spacingDivisorMatrix δ p.2 p.1)^2) :=
    hd.comp_injective (i := fun p : ℕ×ℕ => (p.2,p.1))
      (Equiv.prodComm ℕ ℕ).injective
  have hdiag := spacingDiagonalMatrix_square_summable δ hδ
  have hswap : (∑' p : ℕ×ℕ, (spacingDivisorMatrix δ p.2 p.1)^2) =
      ∑' p : ℕ×ℕ, (spacingDivisorMatrix δ p.1 p.2)^2 :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ×ℕ => (spacingDivisorMatrix δ p.1 p.2)^2)
  simp_rw [spacingNormalizedMatrix_square_split]
  rw [(hd.add ht).tsum_add hdiag,hd.tsum_add ht,hswap,
    spacingDiagonalMatrix_square_tsum,spacingDivisorMatrix_square_tsum δ hδ]
  ring

/-- Every conductor weight above one half gives a Hilbert–Schmidt torsion operator. -/
theorem spacingLimitHilbertOperator_hilbertSchmidt (δ : ℝ) (hδ : 1/2 < δ) :
    (spacingLimitHilbertOperator δ (by linarith)).IsHilbertSchmidt :=
  (spacingLimitHilbertOperator_hilbertSchmidt_iff_matrix δ (by linarith)).mpr
    (spacingNormalizedMatrix_square_summable δ hδ)

#print axioms spacingNormalizedMatrix_square_split
#print axioms spacingDiagonalSquare_summable
#print axioms spacingNormalizedMatrix_square_summable
#print axioms spacingNormalizedMatrix_square_tsum
#print axioms spacingLimitHilbertOperator_hilbertSchmidt

open ArithmeticIntersectionTheory

/-- Every positive even conductor contains the local ramification term at two. -/
theorem spacing_tameDifferent_double_lower (n : ℕ) (hn : 0 < n) :
    Real.log 2≤tameDifferent (2*n) := by
  have hmem : 2∈(2*n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_mul_right 2 n,(Nat.mul_pos (by omega) hn).ne'⟩
  have hs := SelectiveMultiscaleArithmeticPositivity.log_div_le_tameDifferent hmem
  change Real.log 2/((2:ℝ)-1)≤tameDifferent (2*n) at hs
  simpa only [show (2:ℝ)-1=1 by norm_num,div_one] using hs

private def spacingEvenDiagonal (n : ℕ) : ℕ×ℕ :=
  (2*(n+1)-1,2*(n+1)-1)

private theorem spacingEvenDiagonal_injective : Function.Injective spacingEvenDiagonal := by
  intro m n h
  have hh := congrArg Prod.fst h
  change 2*(m+1)-1=2*(n+1)-1 at hh
  omega

/-- Even-conductor diagonals force the sharp necessary square-summability exponent. -/
theorem spacingNormalizedMatrix_half_lt_of_summable (δ : ℝ) (hδ : 0 < δ)
    (hs : Summable (fun p : ℕ×ℕ => (spacingNormalizedMatrix δ p.1 p.2)^2)) :
    1/2 < δ := by
  have heven := hs.comp_injective spacingEvenDiagonal_injective
  let C : ℝ := (2:ℝ)^(-2*δ)*(Real.log 2)^2
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sq_pos_of_pos (Real.log_pos (by norm_num)))
  have hbound (n : ℕ) : C*((n+1:ℕ):ℝ)^(-2*δ) ≤
      (spacingNormalizedMatrix δ (spacingEvenDiagonal n).1 (spacingEvenDiagonal n).2)^2 := by
    have hn := Nat.succ_pos n
    have hn2 : 1≤2*(n+1) := by omega
    have hd := spacing_tameDifferent_double_lower (n+1) hn
    have hl : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    change _≤(spacingNormalizedMatrix δ (2*(n+1)-1) (2*(n+1)-1))^2
    rw [spacingNormalizedMatrix_self_sq,spacingDiagonalSquare,Nat.sub_add_cancel hn2]
    calc C*((n+1:ℕ):ℝ)^(-2*δ) =
          ((2*(n+1):ℕ):ℝ)^(-2*δ)*(Real.log 2)^2 := by
          rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) (by positivity)]
          dsimp only [C]
          ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hd 2)
          (Real.rpow_nonneg (by positivity) _)
  have hCs : Summable (fun n : ℕ => C*((n+1:ℕ):ℝ)^(-2*δ)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
      hbound heven
  have hshift : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(-2*δ)) :=
    (summable_mul_left_iff hC.ne').mp hCs
  have hfull : Summable (fun n : ℕ => (n:ℝ)^(-2*δ)) := by
    have hz (n : ℕ) (hn : n∉Set.range Nat.succ) : (n:ℝ)^(-2*δ)=0 := by
      have hn0 : n=0 := by
        by_contra h
        have hpos : 0 < n := Nat.pos_of_ne_zero h
        apply hn
        exact ⟨n-1,by omega⟩
      rw [hn0,Nat.cast_zero,Real.zero_rpow (by linarith : -2*δ≠0)]
    exact (Nat.succ_injective.summable_iff hz).mp hshift
  have hpow := Real.summable_nat_rpow.mp hfull
  linarith only [hpow]

/-- The actual compact torsion operator is Hilbert–Schmidt exactly above weight one half. -/
theorem spacingLimitHilbertOperator_hilbertSchmidt_iff (δ : ℝ) (hδ : 0 < δ) :
    (spacingLimitHilbertOperator δ hδ).IsHilbertSchmidt ↔ 1/2 < δ := by
  constructor
  · intro hs
    exact spacingNormalizedMatrix_half_lt_of_summable δ hδ
      ((spacingLimitHilbertOperator_hilbertSchmidt_iff_matrix δ hδ).mp hs)
  · exact fun h => spacingLimitHilbertOperator_hilbertSchmidt δ h

/-- The Hilbert–Schmidt norm separates exactly into a prime-ratio product and the tame square sum. -/
theorem spacingLimitHilbertOperator_hsNormSq (δ : ℝ) (hδ : 1/2 < δ) :
    ContinuousLinearMap.hsNormSq (spacingLimitHilbertOperator δ (by linarith)) =
      2*(∑' m : ℕ, ((m+1:ℕ):ℝ)^(-2*δ))*
        (∑' t : ℕ, (Λ (t+1):ℝ)^2*((t+1:ℕ):ℝ)^(-(1+δ)))+
      ∑' n : ℕ, spacingDiagonalSquare δ n := by
  rw [spacingLimitHilbertOperator_hsNormSq_matrix δ (by linarith)
    (spacingLimitHilbertOperator_hilbertSchmidt δ hδ)]
  exact spacingNormalizedMatrix_square_tsum δ hδ

#print axioms spacing_tameDifferent_double_lower
#print axioms spacingNormalizedMatrix_half_lt_of_summable
#print axioms spacingLimitHilbertOperator_hilbertSchmidt_iff
#print axioms spacingLimitHilbertOperator_hsNormSq

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
