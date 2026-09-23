/-
Classical Gauss multiplication value laws for digamma and trigamma.

`GammaMultiplication` supplies the global complex reciprocal-Gamma product.  Its logarithmic
derivative gives the digamma relation; differentiating once more on the common regular locus gives
the trigamma relation.  Both scaled and standard argument forms are exposed.
-/
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.GammaMultiplication

namespace GaloisForLFunctions

open Complex Filter
open scoped Topology

/-- Every finite iterated derivative of `digamma` differentiates to the next one on its regular
locus.  This local form avoids pretending that `digamma` is globally smooth across its pole
lattice. -/
private theorem hasDerivAt_iteratedDeriv_digamma (r : ℕ) {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    HasDerivAt (iteratedDeriv r Complex.digamma)
      (iteratedDeriv (r + 1) Complex.digamma z) z := by
  have hcd := contDiffAt_digamma_n z hz (r + 1)
  have hF : DifferentiableAt ℂ (iteratedFDeriv ℂ r Complex.digamma) z :=
    hcd.differentiableAt_iteratedFDeriv (by
      exact_mod_cast Nat.lt_succ_self r)
  have hd : DifferentiableAt ℂ (iteratedDeriv r Complex.digamma) z := by
    change DifferentiableAt ℂ
      (fun y => (iteratedFDeriv ℂ r Complex.digamma y) (fun _ => 1)) z
    fun_prop
  simpa [iteratedDeriv_succ] using hd.hasDerivAt

/-- **Gauss digamma multiplication, scaled form.**  If `s` is not a Gamma pole, then

`Σ_{k<n} ψ((s+k)/n) = n ψ(s) - n log n`.

The regularity of `s` automatically makes every `(s+k)/n` regular. -/
theorem digamma_multiplication {n : ℕ} (hn : 0 < n) {s : ℂ}
    (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    (∑ k ∈ Finset.range n, Complex.digamma ((s + k) / n)) =
      (n : ℂ) * Complex.digamma s - (n : ℂ) * Complex.log (n : ℂ) := by
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have harg (k : ℕ) : ∀ m : ℕ, (s + (k : ℂ)) / (n : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    apply hs (n * m + k)
    push_cast
    field_simp [hnne] at hm
    linear_combination hm
  let f : ℕ → ℂ → ℂ := fun k w => (Complex.Gamma ((w + (k : ℂ)) / (n : ℂ)))⁻¹
  let g : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹
  have hfun : (fun w : ℂ => ∏ k ∈ Finset.range n, f k w) =
      (fun w : ℂ => (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ w * g w) := by
    funext w
    exact gauss_multiplication_complex hn w
  have hfk_ne : ∀ k ∈ Finset.range n, f k s ≠ 0 := by
    intro k hk
    exact inv_ne_zero (Complex.Gamma_ne_zero (harg k))
  have hfk_diff : ∀ k ∈ Finset.range n, DifferentiableAt ℂ (f k) s := by
    intro k hk
    exact Complex.differentiable_one_div_Gamma.differentiableAt.comp s (by fun_prop)
  have honeLD (w : ℂ) (hw : ∀ m : ℕ, w ≠ -(m : ℂ)) :
      logDeriv g w = -Complex.digamma w := by
    simpa [g, Complex.digamma_def, logDeriv_apply] using
      oneDivGamma_logDeriv_eq_neg_digamma w hw
  have hfkLD : ∀ k ∈ Finset.range n,
      logDeriv (f k) s = -Complex.digamma ((s + (k : ℂ)) / (n : ℂ)) / (n : ℂ) := by
    intro k hk
    have hinner : HasDerivAt (fun w : ℂ => (w + (k : ℂ)) / (n : ℂ))
        ((1 : ℂ) / (n : ℂ)) s := by
      simpa using ((hasDerivAt_id s).add_const (k : ℂ)).div_const (n : ℂ)
    have hcomp := logDeriv_comp
      Complex.differentiable_one_div_Gamma.differentiableAt hinner.differentiableAt
    change logDeriv (f k) s = _
    rw [show f k = g ∘ (fun w : ℂ => (w + (k : ℂ)) / (n : ℂ)) by rfl,
      hcomp, honeLD _ (harg k), hinner.deriv]
    ring
  have hC : (multGammaProd n 1 : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (ne_of_gt (multGammaProd_pos hn one_pos))
  have hpow_ne : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnne)
  have hg_ne : g s ≠ 0 := inv_ne_zero (Complex.Gamma_ne_zero hs)
  have hpow_diff : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ w) s :=
    differentiableAt_id.const_cpow (Or.inl hnne)
  have hA_diff : DifferentiableAt ℂ
      (fun w : ℂ => (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ w) s := by
    fun_prop
  have hg_diff : DifferentiableAt ℂ g s :=
    Complex.differentiable_one_div_Gamma.differentiableAt
  have hpowLD : logDeriv (fun w : ℂ => (n : ℂ) ^ w) s = Complex.log (n : ℂ) := by
    have hd : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w)
        ((n : ℂ) ^ s * Complex.log (n : ℂ)) s := by
      simpa using (hasDerivAt_id s).const_cpow (Or.inl hnne)
    rw [logDeriv_apply, hd.deriv]
    field_simp [hpow_ne]
  have hA_ne : (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ s ≠ 0 :=
    mul_ne_zero hC hpow_ne
  have hrightLD : logDeriv
      (fun w : ℂ => (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ w * g w) s =
      Complex.log (n : ℂ) - Complex.digamma s := by
    rw [logDeriv_mul s hA_ne hg_ne hA_diff hg_diff,
      logDeriv_const_mul s _ hC, hpowLD, honeLD s hs]
    ring
  have hld := congrArg (fun F : ℂ → ℂ => logDeriv F s) hfun
  change logDeriv (∏ k ∈ Finset.range n, f k ·) s =
      logDeriv (fun w : ℂ => (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ w * g w) s at hld
  rw [logDeriv_prod hfk_ne hfk_diff, hrightLD] at hld
  rw [Finset.sum_congr rfl hfkLD] at hld
  have hld' :
      -(∑ k ∈ Finset.range n, Complex.digamma ((s + k) / n)) / (n : ℂ) =
        Complex.log (n : ℂ) - Complex.digamma s := by
    calc
      -(∑ k ∈ Finset.range n, Complex.digamma ((s + k) / n)) / (n : ℂ) =
          (-1 / (n : ℂ)) *
            (∑ k ∈ Finset.range n, Complex.digamma ((s + k) / n)) := by ring
      _ = ∑ k ∈ Finset.range n,
          (-1 / (n : ℂ)) * Complex.digamma ((s + k) / n) := by
            rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range n,
            -Complex.digamma ((s + k) / n) / (n : ℂ) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = _ := hld
  field_simp [hnne] at hld' ⊢
  linear_combination -hld'

/-- **Gauss trigamma multiplication, scaled form.**  On the same regular locus,

`Σ_{k<n} ψ'((s+k)/n) = n² ψ'(s)`.

It is obtained by differentiating `digamma_multiplication` on a neighbourhood that avoids the
Gamma pole lattice. -/
theorem trigamma_multiplication {n : ℕ} (hn : 0 < n) {s : ℂ}
    (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    (∑ k ∈ Finset.range n, deriv Complex.digamma ((s + k) / n)) =
      (n : ℂ) ^ (2 : ℕ) * deriv Complex.digamma s := by
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have harg (k : ℕ) : ∀ m : ℕ, (s + (k : ℂ)) / (n : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    apply hs (n * m + k)
    push_cast
    field_simp [hnne] at hm
    linear_combination hm
  have hGcont : ContinuousAt Complex.Gamma s :=
    (contDiffAt_Gamma s hs 0).continuousAt
  have heq :
      (fun w : ℂ => ∑ k ∈ Finset.range n, Complex.digamma ((w + k) / n)) =ᶠ[𝓝 s]
        (fun w : ℂ => (n : ℂ) * Complex.digamma w -
          (n : ℂ) * Complex.log (n : ℂ)) := by
    filter_upwards [hGcont.eventually_ne (Complex.Gamma_ne_zero hs)] with w hw
    apply digamma_multiplication hn
    intro m hwm
    apply hw
    rw [hwm, Complex.Gamma_neg_nat_eq_zero]
  have hterm : ∀ k ∈ Finset.range n, HasDerivAt
      (fun w : ℂ => Complex.digamma ((w + (k : ℂ)) / (n : ℂ)))
      (deriv Complex.digamma ((s + (k : ℂ)) / (n : ℂ)) / (n : ℂ)) s := by
    intro k hk
    have hdig : HasDerivAt Complex.digamma
        (deriv Complex.digamma ((s + (k : ℂ)) / (n : ℂ)))
        ((s + (k : ℂ)) / (n : ℂ)) :=
      (contDiffAt_digamma_n _ (harg k) 1).differentiableAt (by norm_num) |>.hasDerivAt
    have hinner : HasDerivAt (fun w : ℂ => (w + (k : ℂ)) / (n : ℂ))
        ((1 : ℂ) / (n : ℂ)) s := by
      simpa using ((hasDerivAt_id s).add_const (k : ℂ)).div_const (n : ℂ)
    have hcomp := hdig.comp s hinner
    rw [show
      (fun w : ℂ => Complex.digamma ((w + (k : ℂ)) / (n : ℂ))) =
        Complex.digamma ∘ (fun w : ℂ => (w + (k : ℂ)) / (n : ℂ)) by
      rfl]
    apply hcomp.congr_deriv
    ring
  have hleft : HasDerivAt
      (fun w : ℂ => ∑ k ∈ Finset.range n, Complex.digamma ((w + k) / n))
      (∑ k ∈ Finset.range n,
        deriv Complex.digamma ((s + k) / n) / (n : ℂ)) s := by
    exact HasDerivAt.fun_sum hterm
  have hdig : HasDerivAt Complex.digamma (deriv Complex.digamma s) s :=
    (contDiffAt_digamma_n s hs 1).differentiableAt (by norm_num) |>.hasDerivAt
  have hright : HasDerivAt
      (fun w : ℂ => (n : ℂ) * Complex.digamma w -
        (n : ℂ) * Complex.log (n : ℂ))
      ((n : ℂ) * deriv Complex.digamma s) s :=
    (hdig.const_mul (n : ℂ)).sub_const _
  have hd := heq.deriv_eq
  rw [hleft.deriv, hright.deriv] at hd
  have hd' :
      (∑ k ∈ Finset.range n, deriv Complex.digamma ((s + k) / n)) / (n : ℂ) =
        (n : ℂ) * deriv Complex.digamma s := by
    calc
      (∑ k ∈ Finset.range n, deriv Complex.digamma ((s + k) / n)) / (n : ℂ) =
          ∑ k ∈ Finset.range n,
            deriv Complex.digamma ((s + k) / n) / (n : ℂ) := by
              rw [Finset.sum_div]
      _ = _ := hd
  field_simp [hnne] at hd' ⊢
  linear_combination hd'

/-- **Gauss multiplication for every positive polygamma order.**  For `r ≥ 0`,

`Σ_{k<n} ψ⁽ʳ⁺¹⁾((s+k)/n) = n^(r+2) ψ⁽ʳ⁺¹⁾(s)`.

Thus `r = 0` is trigamma multiplication, and differentiating repeatedly supplies the complete
positive-order multiplication family. -/
theorem polygamma_multiplication (r : ℕ) {n : ℕ} (hn : 0 < n) {s : ℂ}
    (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    (∑ k ∈ Finset.range n,
      iteratedDeriv (r + 1) Complex.digamma ((s + k) / n)) =
      (n : ℂ) ^ (r + 2) * iteratedDeriv (r + 1) Complex.digamma s := by
  induction r generalizing s with
  | zero =>
      simpa [iteratedDeriv_succ] using trigamma_multiplication hn hs
  | succ r ih =>
      have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have harg (k : ℕ) : ∀ m : ℕ, (s + (k : ℂ)) / (n : ℂ) ≠ -(m : ℂ) := by
        intro m hm
        apply hs (n * m + k)
        push_cast
        field_simp [hnne] at hm
        linear_combination hm
      have hGcont : ContinuousAt Complex.Gamma s :=
        (contDiffAt_Gamma s hs 0).continuousAt
      have heq :
          (fun w : ℂ => ∑ k ∈ Finset.range n,
            iteratedDeriv (r + 1) Complex.digamma ((w + k) / n)) =ᶠ[𝓝 s]
          (fun w : ℂ => (n : ℂ) ^ (r + 2) *
            iteratedDeriv (r + 1) Complex.digamma w) := by
        filter_upwards [hGcont.eventually_ne (Complex.Gamma_ne_zero hs)] with w hw
        apply ih
        intro m hwm
        apply hw
        rw [hwm, Complex.Gamma_neg_nat_eq_zero]
      have hterm : ∀ k ∈ Finset.range n, HasDerivAt
          (fun w : ℂ => iteratedDeriv (r + 1) Complex.digamma
            ((w + (k : ℂ)) / (n : ℂ)))
          (iteratedDeriv (r + 2) Complex.digamma
            ((s + (k : ℂ)) / (n : ℂ)) / (n : ℂ)) s := by
        intro k hk
        have hout := hasDerivAt_iteratedDeriv_digamma (r + 1) (harg k)
        have hinner : HasDerivAt (fun w : ℂ => (w + (k : ℂ)) / (n : ℂ))
            ((1 : ℂ) / (n : ℂ)) s := by
          simpa using ((hasDerivAt_id s).add_const (k : ℂ)).div_const (n : ℂ)
        have hcomp := hout.comp s hinner
        rw [show
          (fun w : ℂ => iteratedDeriv (r + 1) Complex.digamma
            ((w + (k : ℂ)) / (n : ℂ))) =
            iteratedDeriv (r + 1) Complex.digamma ∘
              (fun w : ℂ => (w + (k : ℂ)) / (n : ℂ)) by
          rfl]
        apply hcomp.congr_deriv
        ring
      have hleft : HasDerivAt
          (fun w : ℂ => ∑ k ∈ Finset.range n,
            iteratedDeriv (r + 1) Complex.digamma ((w + k) / n))
          (∑ k ∈ Finset.range n,
            iteratedDeriv (r + 2) Complex.digamma ((s + k) / n) / (n : ℂ)) s :=
        HasDerivAt.fun_sum hterm
      have hout := hasDerivAt_iteratedDeriv_digamma (r + 1) hs
      have hright : HasDerivAt
          (fun w : ℂ => (n : ℂ) ^ (r + 2) *
            iteratedDeriv (r + 1) Complex.digamma w)
          ((n : ℂ) ^ (r + 2) * iteratedDeriv (r + 2) Complex.digamma s) s :=
        hout.const_mul _
      have hd := heq.deriv_eq
      rw [hleft.deriv, hright.deriv] at hd
      have hd' :
          (∑ k ∈ Finset.range n,
            iteratedDeriv (r + 2) Complex.digamma ((s + k) / n)) / (n : ℂ) =
            (n : ℂ) ^ (r + 2) * iteratedDeriv (r + 2) Complex.digamma s := by
        rw [Finset.sum_div]
        exact hd
      field_simp [hnne] at hd' ⊢
      convert hd' using 1
      ring

/-- **Half-argument versus unit value at every positive polygamma order.**  Duplication at `s=1`
collapses the two-point orbit to

`ψ⁽ʳ⁺¹⁾(1/2) = (2^(r+2)-1) ψ⁽ʳ⁺¹⁾(1)`.

This is the exact value relation underlying the familiar half-integer zeta factor. -/
theorem polygamma_one_half_eq_mul_one (r : ℕ) :
    iteratedDeriv (r + 1) Complex.digamma (1 / 2 : ℂ) =
      ((2 : ℂ) ^ (r + 2) - 1) * iteratedDeriv (r + 1) Complex.digamma 1 := by
  have h := polygamma_multiplication r (n := 2) (s := (1 : ℂ)) (by norm_num) (by
    intro m hm
    have hre : (1 : ℝ) = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one] at h
  norm_num at h
  linear_combination h

/-- Standard-argument form of Gauss digamma multiplication:
`Σ_{k<n} ψ(z+k/n) = n ψ(nz) - n log n`. -/
theorem digamma_multiplication_rescaled {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ∀ m : ℕ, (n : ℂ) * z ≠ -(m : ℂ)) :
    (∑ k ∈ Finset.range n, Complex.digamma (z + (k : ℂ) / (n : ℂ))) =
      (n : ℂ) * Complex.digamma ((n : ℂ) * z) -
        (n : ℂ) * Complex.log (n : ℂ) := by
  have h := digamma_multiplication hn hz
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnne]

/-- Standard-argument form of Gauss trigamma multiplication:
`Σ_{k<n} ψ'(z+k/n) = n² ψ'(nz)`. -/
theorem trigamma_multiplication_rescaled {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ∀ m : ℕ, (n : ℂ) * z ≠ -(m : ℂ)) :
    (∑ k ∈ Finset.range n, deriv Complex.digamma (z + (k : ℂ) / (n : ℂ))) =
      (n : ℂ) ^ (2 : ℕ) * deriv Complex.digamma ((n : ℂ) * z) := by
  have h := trigamma_multiplication hn hz
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnne]

/-- Standard-argument form of Gauss multiplication for every positive polygamma order:
`Σ_{k<n} ψ⁽ʳ⁺¹⁾(z+k/n) = n^(r+2) ψ⁽ʳ⁺¹⁾(nz)`. -/
theorem polygamma_multiplication_rescaled (r : ℕ) {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ∀ m : ℕ, (n : ℂ) * z ≠ -(m : ℂ)) :
    (∑ k ∈ Finset.range n,
      iteratedDeriv (r + 1) Complex.digamma (z + (k : ℂ) / (n : ℂ))) =
      (n : ℂ) ^ (r + 2) *
        iteratedDeriv (r + 1) Complex.digamma ((n : ℂ) * z) := by
  have h := polygamma_multiplication r hn hz
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnne]

end GaloisForLFunctions
