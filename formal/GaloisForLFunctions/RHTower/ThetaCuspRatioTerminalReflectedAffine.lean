import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalReflectedSecond
import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalReflections

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def amplitudeCross (n : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (n+1),
    Polynomial.C (signedBinomial n i*(5/4:ℂ)^(n-i))*amplitudePoly i

theorem signedBinomial_affine_product {n : ℕ} (he : Even n) (hn : 0<n)
    (Y a : ℂ) (B : ℕ → ℂ) :
    (∑ i ∈ Finset.range (n+1), signedBinomial n i*
      ((Y*B i-3*a^i)*(Y*B (n-i)-3*a^(n-i))))=
      Y^2*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*B (n-i)))-
        6*Y*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*a^(n-i))) := by
  have hp : ∀ i ∈ Finset.range (n+1), a^i*a^(n-i)=a^n := by
    intro i hi
    rw [←pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  have hc : (∑ i ∈ Finset.range (n+1), signedBinomial n i*(B (n-i)*a^i))=
      ∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*a^(n-i)) := by
    calc
      _ = ∑ i ∈ Finset.range (n+1),
          signedBinomial n i*((fun j => B j*a^(n-j)) (n-i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        change signedBinomial n i*(B (n-i)*a^i)=
          signedBinomial n i*(B (n-i)*a^(n-(n-i)))
        rw [Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
      _ = _ := signedBinomial_sum_reflect he (fun j => B j*a^(n-j))
  calc
    _ = Y^2*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*B (n-i)))-
        3*Y*((∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*a^(n-i)))+
          (∑ i ∈ Finset.range (n+1), signedBinomial n i*(B (n-i)*a^i)))+
        9*a^n*(∑ i ∈ Finset.range (n+1), signedBinomial n i) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hiP := hp i hi
      linear_combination 9*signedBinomial n i*hiP
    _ = _ := by rw [hc,signedBinomial_sum_zero hn]; ring

theorem reflection_weight (n i : ℕ) :
    (n.choose i:Poly)*(-1:Poly)^(n-i)=C (signedBinomial n i) := by
  simp only [signedBinomial,map_mul,map_pow,map_neg,map_one,map_natCast]
  ring

theorem reflection_affine {n : ℕ} (he : Even n) (hn : 0<n) :
    reflection n=y^2*liftT (amplitudeSelf n)-6*y*liftT (amplitudeCross n) := by
  apply MvPolynomial.funext
  intro v
  let B : ℕ → ℂ := fun i => eval v (liftT (amplitudePoly i))
  have hH : eval v (liftT (amplitudeSelf n))=
      ∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*B (n-i)) := by
    simp only [amplitudeSelf,map_sum,map_mul,liftT_C,eval_C,B]
  have hK : eval v (liftT (amplitudeCross n))=
      ∑ i ∈ Finset.range (n+1), signedBinomial n i*(B i*(5/4:ℂ)^(n-i)) := by
    simp only [amplitudeCross,map_sum,map_mul,liftT_C,eval_C]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [B]
    ring
  simp only [reflection,reflection_weight,jet_affine,←liftT_amplitudePoly,
    map_sum,map_mul,map_sub,map_pow,map_ofNat,eval_C,hH,hK]
  simpa only [B,mul_assoc] using
    signedBinomial_affine_product he hn (eval v y) (5/4) B

theorem native_reflection_affine {n : ℕ} (he : Even n) (hn : 0<n) :
    pull (integerReflection n)=C ((12:ℂ)^n)*
      (y^2*liftT (amplitudeSelf n)-6*y*liftT (amplitudeCross n)) := by
  rw [pull_integerReflection,reflection_affine he hn]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
