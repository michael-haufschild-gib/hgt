import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSeamRestriction
import GaloisForLFunctions.HTGeometry.PolynomialODE.SeamJetOrderValues

/-! # Exact even source jets through twelve at the algebraic modular seam -/
namespace HTGeometry
noncomputable section

/-- Normalized source derivatives of orders zero through twelve at the seam. -/
def modularThetaEvenSeamSourcePolynomial {K : Type*} [Field K] (n : Fin 7) (X : K) : K :=
  match n.val with
  | 0 => (-3/8) + (1/16)*X^(1 : ℕ)
  | 1 => (15/16) + (-45/64)*X^(1 : ℕ) + (-1/128)*X^(2 : ℕ)
  | 2 => (-285/32) + (225/16)*X^(1 : ℕ) + (191/512)*X^(2 : ℕ) + (51/1024)*X^(3 : ℕ)
  | 3 => (11085/64) + (-118305/256)*X^(1 : ℕ) + (-21683/1024)*X^(2 : ℕ) + (-25755/4096)*X^(3 : ℕ) + (849/8192)*X^(4 : ℕ)
  | 4 => (-720915/128) + (5801175/256)*X^(1 : ℕ) + (1600507/1024)*X^(2 : ℕ) + (782901/1024)*X^(3 : ℕ) + (-892299/32768)*X^(4 : ℕ) + (-26199/65536)*X^(5 : ℕ)
  | 5 => (70335015/256) + (-1588796145/1024)*X^(1 : ℕ) + (-152504033/1024)*X^(2 : ℕ) + (-865949145/8192)*X^(3 : ℕ) + (397222479/65536)*X^(4 : ℕ) + (49594707/262144)*X^(5 : ℕ) + (1341999/524288)*X^(6 : ℕ)
  | _ => (-9603111885/512) + (72410457375/512)*X^(1 : ℕ) + (146977580081/8192)*X^(2 : ℕ) + (281792785791/16384)*X^(3 : ℕ) + (-183992803467/131072)*X^(4 : ℕ) + (-2279863179/32768)*X^(5 : ℕ) + (-4153486905/2097152)*X^(6 : ℕ) + (82018251/4194304)*X^(7 : ℕ)

/-- The full four-state modular recurrence gives every required even seam source jet exactly. -/
theorem eval_modularThetaODESourceJet_even_seam (R : ℂ) (k : Fin 7) :
    MvPolynomial.eval (modularThetaODESeamState R) (modularThetaODESourceJet (2*k.val)) =
      modularThetaEvenSeamSourcePolynomial k (R^(2 : ℕ)) := by
  let v := modularThetaODESeamState R
  let h := evalModularThetaODEFormalJet v .H
  let z := evalModularThetaODEFormalJet v .Z
  let r := evalModularThetaODEFormalJet v .R
  let p := evalModularThetaODEFormalJet v .P
  have hh0 : h 0 = 1 := by simp [h, v, modularThetaODESeamState]
  have hz0 : z 0 = 0 := by simp [z, v, modularThetaODESeamState]
  have hr0 : r 0 = R := by simp [r, v, modularThetaODESeamState]
  have hp0 : p 0 = 0 := by simp [p, v, modularThetaODESeamState]
  have hh (n : ℕ) : h (n+1) = -(1/6:ℂ)*scalarJetConvolution h
      (fun k => p k+scalarJetConvolution r z k) n :=
    evalModularThetaODEFormalJet_H_succ v n
  have hz (n : ℕ) : z (n+1) = -scalarJetConvolution r
      (fun k => scalarJetUnit k-scalarJetConvolution z z k) n :=
    evalModularThetaODEFormalJet_Z_succ v n
  have hr (n : ℕ) : r (n+1) = -(2/3:ℂ)*scalarJetConvolution r
      (fun k => p k+scalarJetConvolution r z k) n :=
    evalModularThetaODEFormalJet_R_succ v n
  have hp (n : ℕ) : p (n+1) = 3*scalarJetUnit n-(1/3:ℂ)*scalarJetConvolution p p n+
      (1/12:ℂ)*scalarJetConvolution (scalarJetConvolution r r)
        (fun k => 3*scalarJetUnit k+scalarJetConvolution z z k) n :=
    evalModularThetaODEFormalJet_P_succ v n
  have J : SeamJetSystem 1 R h z r p :=
    ⟨hh0, hz0, hr0, hp0, hh, hz, hr, hp⟩
  have hh2 := seamJetH2 J
  have hh4 := seamJetH4 J
  have hh6 := seamJetH6 J
  have hh8 := seamJetH8 J
  have hh10 := seamJetH10 J
  have hh12 := seamJetH12 J
  have hh14 := seamJetH14 J
  rw [eval_modularThetaODESourceJet_eq_formalJet]
  change (h (2*k.val+2)-(1/4:ℂ)*h (2*k.val))/2 = _
  fin_cases k <;> norm_num [modularThetaEvenSeamSourcePolynomial, hh0, hh2, hh4, hh6, hh8, hh10, hh12, hh14] <;> ring

end
end HTGeometry
