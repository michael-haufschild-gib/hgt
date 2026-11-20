import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheCovarianceOfMixedZetaDerivatives
import GaloisForLFunctions.CompletedArithmeticForms.GammaSuccessorReserve
import Mathlib.Topology.Instances.Matrix

/-!
# The Gram determinant of consecutive critical zeta jets

At σ=(1+ε)/2 each differentiation multiplies a Dirichlet mode by
minus its log frequency. The rescaled mixed second moments have the
signed factorial Hankel matrix as their limit. Its determinant gives
both the precise blowup exponent d² and the product of squared
factorials for the first d derivatives of the same random series.
-/

noncomputable section
open Finset Filter Topology Complex Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.CompletedArithmeticForms
open scoped ComplexConjugate
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

private def jetPoint (ε : ℝ) : ℂ := 1/2+(ε:ℂ)*(1/2)

/-- The finite Gram section uses the common random phases for all jets. -/
def steinhausJetGram (d N : ℕ) (ε : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => mixedJetMoment N i.val j.val (jetPoint ε) (jetPoint ε)

/-- Infinite-cutoff Gram section at distance ε/2 from the critical line. -/
def limitingJetGram (d : ℕ) (ε : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => iteratedDeriv (i.val+j.val) riemannZeta (1+(ε:ℂ))

private theorem point_pair (ε : ℝ) : jetPoint ε+conj (jetPoint ε)=1+(ε:ℂ) := by
  simp only [jetPoint,map_add,map_mul,map_div₀,map_one,map_ofNat,conj_ofReal]
  ring

theorem steinhaus_jet_gram_limit (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => steinhausJetGram d N ε) atTop (𝓝 (limitingJetGram d ε)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h : 1 < (jetPoint ε).re+(jetPoint ε).re := by
    have H := congrArg re (point_pair ε)
    simp only [add_re,conj_re,one_re,ofReal_re] at H
    linarith only [H,hε]
  simpa only [steinhausJetGram,limitingJetGram,point_pair] using mixed_jet_zeta_kernel i.val j.val h

private def signedFactorialGram (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (-1:ℂ)^(i.val+j.val)*((i.val+j.val).factorial:ℂ)

private theorem critical_entry (d : ℕ) (i j : Fin d) :
    Tendsto (fun ε : ℝ => (ε:ℂ)^(i.val+j.val+1)*limitingJetGram d ε i j) (𝓝[>] 0)
      (𝓝 (signedFactorialGram d i j)) := by
  obtain ⟨F,hN,hF⟩ := critical_mixed_jet_limit i.val j.val (u:=1/2) (v:=1/2) (by norm_num)
  have H (ε : ℝ) (hε : 0 < ε) : F ε = limitingJetGram d ε i j := by
    have hG := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (steinhaus_jet_gram_limit d hε) i) j
    exact tendsto_nhds_unique (hN ε hε) hG
  have hden : (1/2:ℂ)+conj (1/2:ℂ)=1 := by
    rw [map_div₀,map_one,map_ofNat]
    norm_num
  rw [hden,one_pow,div_one] at hF
  apply hF.congr'
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Set.Ioi (0:ℝ))] with ε hε
  rw [H ε hε]

private theorem signed_factorial_det (d : ℕ) :
    (signedFactorialGram d).det = ∏ i : Fin d, (i.val.factorial:ℂ)^2 := by
  have hshape (n : ℕ) : gammaShapeMoment 1 n = (n.factorial:ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [gammaShapeMoment_succ,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring
  let M := finiteHankelMatrix (scaledGammaMoment 1 (-1) 1) d
  have he : signedFactorialGram d = ofRealHom.mapMatrix M := by
    ext i j
    change (-1:ℂ)^(i.val+j.val)*((i.val+j.val).factorial:ℂ) =
      ((1*(-1:ℝ)^(i.val+j.val)*gammaShapeMoment 1 (i.val+j.val):ℝ):ℂ)
    rw [hshape,one_mul,ofReal_mul,ofReal_pow,ofReal_neg,ofReal_one,ofReal_natCast]
  rw [he,←ofRealHom.map_det]
  change (↑((finiteHankelMatrix (scaledGammaMoment 1 (-1) 1) d).det):ℂ) = _
  rw [det_scaledGammaHankel,ofReal_prod]
  apply prod_congr rfl
  intro i _
  rw [(even_two_mul i.val).neg_one_pow,hshape]
  simp only [one_mul,ofReal_mul,ofReal_natCast,pow_two]

private theorem scaled_jet_det (ε : ℂ) (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.of fun i j : Fin d => ε^(i.val+j.val+1)*A i j).det = ε^(d^2)*A.det := by
  let B := Matrix.of fun i j : Fin d => ε^j.val*A i j
  have h : (Matrix.of fun i j : Fin d => ε^(i.val+j.val+1)*A i j) =
      Matrix.of fun i j : Fin d => ε^(i.val+1)*B i j := by
    ext i j
    simp only [Matrix.of_apply,B,←mul_assoc,←pow_add]
    rw [Nat.add_right_comm]
  have hp (n : ℕ) : (∏ i : Fin n, ε^(i.val+1+i.val)) = ε^(n^2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,ih,←pow_add]
      congr 1
      ring
  rw [h,Matrix.det_mul_column,show B.det = _ from Matrix.det_mul_row _ A,←mul_assoc,
    ←prod_mul_distrib]
  simp only [←pow_add,hp]

/-- The first d random zeta jets have Gram determinant asymptotic to
ε^(-d²) times ∏(i!)², with the Dirichlet cutoff taken first. -/
theorem critical_jet_gram_determinant (d : ℕ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N => (steinhausJetGram d N ε).det) atTop
      (𝓝 (limitingJetGram d ε).det)) ∧
    Tendsto (fun ε : ℝ => (ε:ℂ)^(d^2)*(limitingJetGram d ε).det) (𝓝[>] 0)
      (𝓝 (∏ i : Fin d, (i.val.factorial:ℂ)^2)) := by
  have hdet : Continuous (Matrix.det : Matrix (Fin d) (Fin d) ℂ → ℂ) :=
    continuous_id.matrix_det
  refine ⟨fun ε hε => hdet.continuousAt.tendsto.comp (steinhaus_jet_gram_limit d hε),?_⟩
  let T (ε : ℝ) := Matrix.of fun i j : Fin d => (ε:ℂ)^(i.val+j.val+1)*limitingJetGram d ε i j
  have H : Tendsto T (𝓝[>] 0) (𝓝 (signedFactorialGram d)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => critical_entry d i j
  have h := hdet.continuousAt.tendsto.comp H
  change Tendsto (fun ε => (T ε).det) _ (𝓝 (signedFactorialGram d).det) at h
  simpa only [T,scaled_jet_det,signed_factorial_det] using h


end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
