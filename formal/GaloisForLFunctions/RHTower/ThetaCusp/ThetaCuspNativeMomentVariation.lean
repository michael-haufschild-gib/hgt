import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenSeamJets
/-!
# Exact center variations of every native reflected source jet

Finite Leibniz sums retain the complete theta source and identify its
first and second center variations at every order. These variations
supply the cofactor-curvature sign test without a derivative premise.
-/

namespace RHTower.ThetaOddMomentVariation
noncomputable section
private def f (n : ℕ) := iteratedDeriv n thetaCuspFullSource
private theorem df (n : ℕ) (x : ℝ) : HasDerivAt (f n) (f (n+1) x) x := by
  unfold f
  simp_rw [iteratedDeriv_thetaCuspFullSource]
  exact hasDerivAt_thetaCuspFullDerivative n x

def jetFirst (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*(-1:ℝ)^(n-i)*
    (f (i+1) x*f (n-i) x+f i x*f (n-i+1) x)

def jetSecond (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*(-1:ℝ)^(n-i)*
    (f (i+2) x*f (n-i) x+2*f (i+1) x*f (n-i+1) x+f i x*f (n-i+2) x)

theorem native_first (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspNativeReflectionJet n) (jetFirst n x) x := by
  have h := HasDerivAt.fun_sum (u:=Finset.range (n+1)) (fun i _ =>
    (((df i x).mul (df (n-i) x)).const_mul ((n.choose i:ℝ)*(-1:ℝ)^(n-i))))
  simp only [Pi.mul_apply] at h
  have he : (fun y => ∑ i ∈ Finset.range (n+1),
      (n.choose i:ℝ)*(-1:ℝ)^(n-i)*(f i y*f (n-i) y))=thetaCuspNativeReflectionJet n := by
    funext y
    rw [thetaCuspNativeReflectionJet_eq]
    apply Finset.sum_congr rfl
    intro i _
    unfold f
    ring
  rw [he] at h
  exact h

theorem native_second (n : ℕ) (x : ℝ) : HasDerivAt (jetFirst n) (jetSecond n x) x := by
  have h := HasDerivAt.fun_sum (u:=Finset.range (n+1)) (fun i _ =>
    ((((df (i+1) x).mul (df (n-i) x)).add
      ((df i x).mul (df (n-i+1) x))).const_mul ((n.choose i:ℝ)*(-1:ℝ)^(n-i))))
  convert h using 1 <;> first | rfl | {
    unfold jetSecond
    apply Finset.sum_congr rfl
    intro i _
    ring }

end
end RHTower.ThetaOddMomentVariation
