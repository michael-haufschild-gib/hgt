import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticParityMellin
import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential

/-!
# Exact parity deletion for the source Dirichlet convolution

The odd restriction respects Dirichlet convolution. Applied to the source
convolution with two constant sequences, this identifies the alternating
Dirichlet series with the full series and its even restriction.
-/

open Complex Set Filter Topology
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSingularArithmetic

def evenPart (f : ℕ → ℂ) (n : ℕ) : ℂ := if 2 ∣ n then f n else 0
def oddPart (f : ℕ → ℂ) (n : ℕ) : ℂ := if 2 ∣ n then 0 else f n

theorem oddPart_eq_sub (f : ℕ → ℂ) : oddPart f = f - evenPart f := by
  funext n
  by_cases hn : 2 ∣ n <;> simp [oddPart, evenPart, hn]

theorem summable_evenPart {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (evenPart f) s := by
  have h := hf.indicator {n | 2 ∣ n}
  refine h.congr fun n => ?_
  by_cases hn : 2 ∣ n <;> simp [evenPart, LSeries.term, hn]

theorem summable_oddPart {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (oddPart f) s := by
  rw [oddPart_eq_sub]
  exact hf.sub (summable_evenPart hf)

theorem oddPart_convolution (f g : ℕ → ℂ) :
    oddPart (LSeries.convolution f g) = LSeries.convolution (oddPart f) (oddPart g) := by
  funext n
  rw [LSeries.convolution_def]
  change (if 2 ∣ n then 0 else ∑ p ∈ n.divisorsAntidiagonal, f p.1*g p.2) = _
  rw [LSeries.convolution_def]
  have he : (if 2 ∣ n then 0 else ∑ p ∈ n.divisorsAntidiagonal, f p.1*g p.2) =
      ∑ p ∈ n.divisorsAntidiagonal, (if 2 ∣ n then 0 else f p.1*g p.2) := by
    by_cases h : 2 ∣ n <;> simp [h]
  rw [he]
  apply Finset.sum_congr rfl
  intro p hp
  have hn := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hd : 2 ∣ n ↔ 2 ∣ p.1 ∨ 2 ∣ p.2 := hn ▸ Nat.prime_two.dvd_mul
  by_cases h1 : 2 ∣ p.1 <;> by_cases h2 : 2 ∣ p.2 <;>
    simp [oddPart, hd, h1, h2]

theorem LSeries_evenPart_one {s : ℂ} (hs : 1 < s.re) :
    LSeries (evenPart 1) s = (2 : ℂ)^(-s) * riemannZeta s := by
  have hinj : Function.Injective (fun n : ℕ => 2*n) := fun a b h => by dsimp at h; omega
  have hsupport : Function.support (LSeries.term (evenPart 1) s) ⊆
      Set.range (fun n : ℕ => 2*n) := by
    intro n hn
    by_cases hd : 2 ∣ n
    · rcases hd with ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · exact False.elim (hn (by simp [LSeries.term, evenPart, hd]))
  have ht (n : ℕ) : LSeries.term (evenPart 1) s (2*n) =
      (2 : ℂ)^(-s) * LSeries.term 1 s n := by
    by_cases hn : n = 0
    · simp [hn, LSeries.term]
    · have h2n : 2*n ≠ 0 := by omega
      simp only [LSeries.term, if_neg hn, if_neg h2n, evenPart, dvd_mul_right,
        if_true, Pi.one_apply, Nat.cast_mul, Nat.cast_ofNat]
      have he := Complex.mul_cpow_ofReal_nonneg (a := 2) (b := (n : ℝ))
        (by norm_num) (Nat.cast_nonneg n) s
      norm_num only [Complex.ofReal_ofNat, Complex.ofReal_natCast] at he
      rw [he, Complex.cpow_neg]
      simp only [one_div, mul_inv]
  rw [LSeries, ← hinj.tsum_eq hsupport]
  simp_rw [ht]
  rw [tsum_mul_left, ← LSeries, LSeries_one_eq_riemannZeta hs]

theorem LSeries_oddPart_one {s : ℂ} (hs : 1 < s.re) :
    LSeries (oddPart 1) s = (1-(2 : ℂ)^(-s))*riemannZeta s := by
  rw [oddPart_eq_sub, LSeries_sub (LSeriesSummable_one_iff.mpr hs)
    (summable_evenPart (LSeriesSummable_one_iff.mpr hs)),
    LSeries_evenPart_one hs, LSeries_one_eq_riemannZeta hs]
  ring

theorem alternating_eq_sub_twice_oddPart (f : ℕ → ℂ) :
    (fun n => f n * (-1 : ℂ)^n) = f - (2 : ℂ) • oddPart f := by
  funext n
  by_cases hn : Even n
  · have hd : 2 ∣ n := even_iff_two_dvd.mp hn
    simp [hn.neg_one_pow, oddPart, hd]
  · have ho : Odd n := Nat.not_even_iff_odd.mp hn
    have hd : ¬ 2 ∣ n := fun hd => hn (even_iff_two_dvd.mpr hd)
    simp [ho.neg_one_pow, oddPart, hd]
    ring

theorem LSeries_sourceAlternating_deletion {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    let d : ℕ → ℂ := WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
    sourceAlternatingZetaSquare lam s = (riemannZeta s)^2 *
      ((-1+4*(2 : ℂ)^(-s)-2*((2 : ℂ)^(-s))^2)*LSeries d s +
        2*(1-(2 : ℂ)^(-s))^2*LSeries (evenPart d) s) := by
  dsimp only
  let d : ℕ → ℂ := WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hd : LSeriesSummable d s := LSeriesSummable.sub (WeilHerglotz.summable_term_lamC hW hs)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hb : LSeriesSummable (sourceSquareCoeff lam) s := sourceSquareCoeff_summable hW hs
  have hid : oddPart (sourceSquareCoeff lam) = LSeries.convolution
      (LSeries.convolution (oddPart d) (oddPart 1)) (oddPart 1) := by
    rw [sourceSquareCoeff, oddPart_convolution, oddPart_convolution]
  have hfull : LSeries (sourceSquareCoeff lam) s = LSeries d s*(riemannZeta s)^2 := by
    rw [sourceSquareCoeff, LSeries_convolution' (hd.convolution h1) h1,
      LSeries_convolution' hd h1, LSeries_one_eq_riemannZeta hs]
    ring
  have hodd : LSeries (oddPart (sourceSquareCoeff lam)) s =
      (LSeries d s - LSeries (evenPart d) s)*((1-(2 : ℂ)^(-s))*riemannZeta s)^2 := by
    rw [hid, LSeries_convolution' ((summable_oddPart hd).convolution (summable_oddPart h1))
        (summable_oddPart h1), LSeries_convolution' (summable_oddPart hd) (summable_oddPart h1),
      LSeries_oddPart_one hs, oddPart_eq_sub d, LSeries_sub hd (summable_evenPart hd)]
    ring
  unfold sourceAlternatingZetaSquare sourceAlternatingCoeff
  rw [alternating_eq_sub_twice_oddPart, LSeries_sub hb ((summable_oddPart hb).smul 2),
    LSeries_smul, hfull, hodd]
  ring
open GaloisForLFunctions.HTGeometry

theorem oddPart_dirichletConvPow (f : ℕ → ℂ) (k : ℕ) :
    oddPart (dirichletConvPow f k) = dirichletConvPow (oddPart f) k := by
  induction k with
  | zero =>
    funext n
    by_cases hn : n=1
    · subst n
      simp [oddPart,dirichletConvPow]
    · simp [oddPart,dirichletConvPow,hn]
  | succ k ih =>
    rw [dirichletConvPow_succ,oddPart_convolution,ih,dirichletConvPow_succ]

theorem oddPart_dirichletExp (f : ℕ → ℂ) :
    oddPart (dirichletExp f) = dirichletExp (oddPart f) := by
  funext n
  have h (k : ℕ) := congrFun (oddPart_dirichletConvPow f k) n
  by_cases hn : 2 ∣ n
  · simp only [oddPart,hn,if_true]
    unfold dirichletExp
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [← h k]
    simp [oddPart,hn]
  · simp only [oddPart,hn,if_false,dirichletExp]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    simpa [oddPart,hn] using h k

end RHTower.WeilWorkSettledPhase
