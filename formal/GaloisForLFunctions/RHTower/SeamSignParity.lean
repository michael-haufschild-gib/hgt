/-
Real-zero parity on the seam: the endpoint sign flip reads the total on-line vanishing order.

On the critical line `s = ½+iτ` a functional-equation + Schwarz-symmetric member is real, so where it
does not vanish its real restriction carries a sign.  Presented in factored form
`f(linePt τ) = (∏_{τ'} (linePt τ − linePt τ')^{m τ'})·h(linePt τ)` with `h` continuous and nonvanishing
on the window and the on-line zeros `τ'` strictly interior, the difference `linePt τ − linePt τ' =
(τ−τ')·i` turns the product into a real amplitude `∏ (τ−τ')^{m τ'}` times the constant phase `i^{Σ m}`.
The real part then factors as `P(τ)·v(τ)` with `P(τ) = ∏ (τ−τ')^{m τ'}` real and
`v = Re(i^{Σ m}·h∘linePt)` continuous and nonvanishing on the segment — reality off the finite zero set
extends by continuity to the whole segment — hence of constant sign.  The endpoint product of real parts
is `P(τ₁)P(τ₂)` up to a positive factor, and `P(τ₁)P(τ₂)` carries the sign `(−1)^{Σ m}` because each
interior zero contributes a strictly negative `(τ₁−τ')(τ₂−τ')`.  Thus the seam sign flips across the
window exactly when the total on-line order `Σ m` is odd — the parity of a real-line cluster is a seam
observable.  Composed with the undeformability of a seam sign bracket (`online_zero_pinned_of_sign_bracket`),
an odd-total on-line cluster cannot be pushed off the critical line while the window endpoints stay
nonvanishing; off-line zeros, whose reflection-symmetric totals are even, carry no such constraint.
-/
import GaloisForLFunctions.RHTower.SeamSignBit

open Complex

namespace RHTower

/-- The two line points differ by a purely imaginary shift: `linePt τ − linePt τ' = (τ − τ')·i`. -/
private lemma linePt_sub (τ τ' : ℝ) : linePt τ - linePt τ' = ((τ - τ' : ℝ) : ℂ) * I := by
  unfold linePt
  rw [Complex.ofReal_sub]
  ring

/-- **Amplitude/phase split of the factored line product.**  Since each factor is
`(linePt τ − linePt τ')^{m τ'} = ((τ − τ')·i)^{m τ'}`, the moduli collect into a real amplitude and the
imaginary units into a single constant phase:
`∏ (linePt τ − linePt τ')^{m τ'} = (∏ (τ − τ')^{m τ'} : ℝ)·i^{Σ m τ'}`. -/
private lemma prodC_eq (zs : Finset ℝ) (m : ℝ → ℕ) (τ : ℝ) :
    (∏ τ' ∈ zs, (linePt τ - linePt τ') ^ m τ')
      = ((∏ τ' ∈ zs, (τ - τ') ^ m τ' : ℝ) : ℂ) * I ^ (∑ τ' ∈ zs, m τ') := by
  rw [Complex.ofReal_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro τ' _
  rw [linePt_sub, mul_pow, Complex.ofReal_pow]

/-- **Endpoint amplitude product carries the sign `(−1)^{Σ m}`.**  A pure ring identity per factor
(`(τ₁−τ')(τ₂−τ') = (−1)·(τ'−τ₁)(τ₂−τ')`) gives
`(∏ (τ₁ − τ')^{m τ'})·(∏ (τ₂ − τ')^{m τ'}) = (−1)^{Σ m τ'}·∏ ((τ' − τ₁)(τ₂ − τ'))^{m τ'}`. -/
private lemma prodR_sign (zs : Finset ℝ) (m : ℝ → ℕ) (τ₁ τ₂ : ℝ) :
    (∏ τ' ∈ zs, (τ₁ - τ') ^ m τ') * (∏ τ' ∈ zs, (τ₂ - τ') ^ m τ')
      = (-1) ^ (∑ τ' ∈ zs, m τ') * ∏ τ' ∈ zs, ((τ' - τ₁) * (τ₂ - τ')) ^ m τ' := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro τ' _
  have hbase : (τ₁ - τ') * (τ₂ - τ') = (-1) * ((τ' - τ₁) * (τ₂ - τ')) := by ring
  rw [← mul_pow, ← mul_pow, hbase]

/-- **A never-zero continuous function keeps one sign on a segment.**  If `v` is continuous and
nonvanishing on `[τ₁, τ₂]`, the intermediate value theorem forbids a sign change, so its endpoint values
have equal sign and their product is positive. -/
private lemma real_endpoint_sign_prod {v : ℝ → ℝ} {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂)
    (hc : ContinuousOn v (Set.Icc τ₁ τ₂)) (hne : ∀ τ ∈ Set.Icc τ₁ τ₂, v τ ≠ 0) :
    0 < v τ₁ * v τ₂ := by
  have hm₁ : τ₁ ∈ Set.Icc τ₁ τ₂ := Set.left_mem_Icc.mpr hτ
  have hm₂ : τ₂ ∈ Set.Icc τ₁ τ₂ := Set.right_mem_Icc.mpr hτ
  have hsign : 0 < v τ₁ ↔ 0 < v τ₂ := by
    constructor
    · intro h1
      by_contra h2
      have h2' : v τ₂ < 0 := lt_of_le_of_ne (not_lt.mp h2) (hne τ₂ hm₂)
      obtain ⟨c, hcmem, hc0⟩ := intermediate_value_Icc' hτ hc ⟨h2'.le, h1.le⟩
      exact hne c hcmem hc0
    · intro h2
      by_contra h1
      have h1' : v τ₁ < 0 := lt_of_le_of_ne (not_lt.mp h1) (hne τ₁ hm₁)
      obtain ⟨c, hcmem, hc0⟩ := intermediate_value_Icc hτ hc ⟨h1'.le, h2.le⟩
      exact hne c hcmem hc0
  rcases lt_or_gt_of_ne (hne τ₁ hm₁) with h1 | h1
  · have h2 : v τ₂ < 0 :=
      lt_of_le_of_ne (not_lt.mp (fun hp => absurd (hsign.mpr hp) (not_lt.mpr h1.le))) (hne τ₂ hm₂)
    exact mul_pos_of_neg_of_neg h1 h2
  · exact mul_pos h1 (hsign.mp h1)

/-- **Seam sign flip reads the parity of the total on-line order.**  For a member real on the segment
`[τ₁, τ₂]` of the critical line, presented as `f(linePt τ) = (∏ (linePt τ − linePt τ')^{m τ'})·h(linePt τ)`
with `h` continuous and nonvanishing on the segment and the on-line zeros `τ'` strictly interior, the
product of the real restrictions at the endpoints is negative — the seam sign flips — exactly when the
total on-line vanishing order `Σ m τ'` is odd.

The imaginary shift `linePt τ − linePt τ' = (τ − τ')·i` splits the factor into a real amplitude
`P(τ) = ∏ (τ − τ')^{m τ'}` and the constant phase `i^{Σ m}`; writing `w(τ) = i^{Σ m}·h(linePt τ)`,
reality of `f` forces `Im w = 0` off the finite zero set, hence everywhere on the segment by continuity
(the complement of the finite zero set is dense), so `Re w` is continuous and nonvanishing and keeps one
sign.  The endpoint real-part product is `P(τ₁)P(τ₂)` times the positive `Re w(τ₁)·Re w(τ₂)`, and
`P(τ₁)P(τ₂) = (−1)^{Σ m}·(positive)` because each interior zero gives `(τ₁ − τ')(τ₂ − τ') < 0`. -/
theorem line_sign_flip_iff_odd_total_order
    {h : ℂ → ℂ} {zs : Finset ℝ} {m : ℝ → ℕ} {τ₁ τ₂ : ℝ} {f : ℂ → ℂ}
    (hτ : τ₁ < τ₂)
    (hz : ∀ τ' ∈ zs, τ₁ < τ' ∧ τ' < τ₂)
    (hfact : ∀ τ ∈ Set.Icc τ₁ τ₂,
      f (linePt τ) = (∏ τ' ∈ zs, (linePt τ - linePt τ') ^ m τ') * h (linePt τ))
    (hhc : Continuous fun τ : ℝ => h (linePt τ))
    (hh0 : ∀ τ ∈ Set.Icc τ₁ τ₂, h (linePt τ) ≠ 0)
    (hreal : ∀ τ ∈ Set.Icc τ₁ τ₂, (f (linePt τ)).im = 0) :
    ((f (linePt τ₁)).re * (f (linePt τ₂)).re < 0 ↔ Odd (∑ τ' ∈ zs, m τ')) := by
  have hwcont : Continuous fun τ : ℝ => I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ) :=
    continuous_const.mul hhc
  -- `Im w` vanishes wherever the real amplitude is nonzero, i.e. off the finite zero set.
  have himW_eqon : Set.EqOn (fun τ : ℝ => (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).im)
      (fun _ => (0 : ℝ)) (Set.Icc τ₁ τ₂ \ (↑zs : Set ℝ)) := by
    intro τ hτmem
    have hτIcc : τ ∈ Set.Icc τ₁ τ₂ := hτmem.1
    have hPne : (∏ τ' ∈ zs, (τ - τ') ^ m τ') ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro τ' hτ'mem
      have hne : τ ≠ τ' := by rintro rfl; exact hτmem.2 (Finset.mem_coe.mpr hτ'mem)
      exact pow_ne_zero _ (sub_ne_zero.mpr hne)
    have hfim : (f (linePt τ)).im
        = (∏ τ' ∈ zs, (τ - τ') ^ m τ') * (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).im := by
      rw [hfact τ hτIcc, prodC_eq zs m τ, mul_assoc, Complex.im_ofReal_mul]
    have hz0 : (∏ τ' ∈ zs, (τ - τ') ^ m τ') * (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).im = 0 := by
      rw [← hfim]; exact hreal τ hτIcc
    exact (mul_eq_zero.mp hz0).resolve_left hPne
  have himW_cont : Continuous fun τ : ℝ => (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).im :=
    Complex.continuous_im.comp hwcont
  -- the complement of a finite set is dense, so the segment lies in the closure of its zero-free part.
  have hdense : Dense ((↑zs : Set ℝ)ᶜ) := Set.Countable.dense_compl ℝ zs.finite_toSet.countable
  have hIcc_sub : Set.Icc τ₁ τ₂ ⊆ closure (Set.Icc τ₁ τ₂ \ (↑zs : Set ℝ)) := by
    have h1 : Set.Ioo τ₁ τ₂ ⊆ closure (Set.Ioo τ₁ τ₂ ∩ (↑zs : Set ℝ)ᶜ) :=
      hdense.open_subset_closure_inter isOpen_Ioo
    have h2 : Set.Ioo τ₁ τ₂ ∩ (↑zs : Set ℝ)ᶜ ⊆ Set.Icc τ₁ τ₂ \ (↑zs : Set ℝ) := by
      intro x hx; exact ⟨Set.Ioo_subset_Icc_self hx.1, hx.2⟩
    have h3 : Set.Ioo τ₁ τ₂ ⊆ closure (Set.Icc τ₁ τ₂ \ (↑zs : Set ℝ)) :=
      h1.trans (closure_mono h2)
    calc Set.Icc τ₁ τ₂ = closure (Set.Ioo τ₁ τ₂) := (closure_Ioo (ne_of_lt hτ)).symm
      _ ⊆ closure (closure (Set.Icc τ₁ τ₂ \ (↑zs : Set ℝ))) := closure_mono h3
      _ = closure (Set.Icc τ₁ τ₂ \ (↑zs : Set ℝ)) := closure_closure
  have himW_all : ∀ τ ∈ Set.Icc τ₁ τ₂, (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).im = 0 := by
    intro τ hτmem
    exact himW_eqon.closure himW_cont continuous_const (hIcc_sub hτmem)
  -- `Re w` is therefore nonvanishing on the segment.
  have hv_ne : ∀ τ ∈ Set.Icc τ₁ τ₂, (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).re ≠ 0 := by
    intro τ hτmem hre0
    have hw0 : I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ) = 0 := by
      apply Complex.ext
      · rw [hre0, Complex.zero_re]
      · rw [himW_all τ hτmem, Complex.zero_im]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (hh0 τ hτmem) hw0
  have hv_cont : ContinuousOn (fun τ : ℝ => (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).re)
      (Set.Icc τ₁ τ₂) := (Complex.continuous_re.comp hwcont).continuousOn
  have hpv : 0 < (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ₁)).re
      * (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ₂)).re :=
    real_endpoint_sign_prod hτ.le hv_cont hv_ne
  -- the endpoint real parts factor through the real amplitude.
  have hg : ∀ τ ∈ Set.Icc τ₁ τ₂, (f (linePt τ)).re
      = (∏ τ' ∈ zs, (τ - τ') ^ m τ') * (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ)).re := by
    intro τ hτmem
    rw [hfact τ hτmem, prodC_eq zs m τ, mul_assoc, Complex.re_ofReal_mul]
  have hQpos : 0 < ∏ τ' ∈ zs, ((τ' - τ₁) * (τ₂ - τ')) ^ m τ' := by
    apply Finset.prod_pos
    intro τ' hτ'mem
    obtain ⟨hl, hr⟩ := hz τ' hτ'mem
    exact pow_pos (mul_pos (sub_pos.mpr hl) (sub_pos.mpr hr)) _
  have hpos : 0 < (∏ τ' ∈ zs, ((τ' - τ₁) * (τ₂ - τ')) ^ m τ')
      * ((I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ₁)).re
        * (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ₂)).re) := mul_pos hQpos hpv
  have hprod : (f (linePt τ₁)).re * (f (linePt τ₂)).re
      = ((∏ τ' ∈ zs, (τ₁ - τ') ^ m τ') * (∏ τ' ∈ zs, (τ₂ - τ') ^ m τ'))
        * ((I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ₁)).re
          * (I ^ (∑ τ' ∈ zs, m τ') * h (linePt τ₂)).re) := by
    rw [hg τ₁ (Set.left_mem_Icc.mpr hτ.le), hg τ₂ (Set.right_mem_Icc.mpr hτ.le)]
    ring
  rw [hprod, prodR_sign zs m τ₁ τ₂, mul_assoc]
  rcases Nat.even_or_odd (∑ τ' ∈ zs, m τ') with he | ho
  · rw [Even.neg_one_pow he, one_mul]
    exact iff_of_false (not_lt.mpr hpos.le) (Nat.not_odd_iff_even.mpr he)
  · rw [Odd.neg_one_pow ho, neg_one_mul]
    exact iff_of_true (neg_lt_zero.mpr hpos) ho

/-- **Pinning dichotomy for an odd on-line cluster.**  Given a deformation `F` whose two line anchors
`linePt τ₁`, `linePt τ₂` stay continuous, real, and nonvanishing in time, whose final slice `F 1` is
continuous and real along the segment, and whose initial slice `F 0` has the factored on-line
presentation of `line_sign_flip_iff_odd_total_order` with total order `Σ m` odd, some on-line zero of the
final slice survives in `[τ₁, τ₂]`.  The parity theorem turns the odd total order into a time-`0` seam
sign bracket (product of endpoint real parts negative), and `online_zero_pinned_of_sign_bracket`
transports that bracket to the final time.  An odd-total-order on-line cluster can never be deformed off
the critical line while the window's endpoints stay nonvanishing — the seam sign is the conserved
quantity that pins it; off-line zeros, having even reflection-symmetric totals, are exactly the defects
free of this constraint. -/
theorem online_odd_cluster_pinned
    {F : ℝ → ℂ → ℂ} {h : ℂ → ℂ} {zs : Finset ℝ} {m : ℝ → ℕ} {τ₁ τ₂ : ℝ}
    (hτ : τ₁ < τ₂)
    (hz : ∀ τ' ∈ zs, τ₁ < τ' ∧ τ' < τ₂)
    (hc₁ : Continuous fun t : ℝ => F t (linePt τ₁))
    (hc₂ : Continuous fun t : ℝ => F t (linePt τ₂))
    (hreal₁ : ∀ t : ℝ, (F t (linePt τ₁)).im = 0)
    (hreal₂ : ∀ t : ℝ, (F t (linePt τ₂)).im = 0)
    (hnv₁ : ∀ t : ℝ, F t (linePt τ₁) ≠ 0)
    (hnv₂ : ∀ t : ℝ, F t (linePt τ₂) ≠ 0)
    (hline : Continuous fun τ : ℝ => F 1 (linePt τ))
    (hreal_seg : ∀ τ ∈ Set.Icc τ₁ τ₂, (F 1 (linePt τ)).im = 0)
    (hfact : ∀ τ ∈ Set.Icc τ₁ τ₂,
      F 0 (linePt τ) = (∏ τ' ∈ zs, (linePt τ - linePt τ') ^ m τ') * h (linePt τ))
    (hhc : Continuous fun τ : ℝ => h (linePt τ))
    (hh0 : ∀ τ ∈ Set.Icc τ₁ τ₂, h (linePt τ) ≠ 0)
    (hreal0 : ∀ τ ∈ Set.Icc τ₁ τ₂, (F 0 (linePt τ)).im = 0)
    (hodd : Odd (∑ τ' ∈ zs, m τ')) :
    ∃ τ ∈ Set.Icc τ₁ τ₂, F 1 (linePt τ) = 0 := by
  have hbracket : (F 0 (linePt τ₁)).re * (F 0 (linePt τ₂)).re < 0 :=
    (line_sign_flip_iff_odd_total_order (f := F 0) hτ hz hfact hhc hh0 hreal0).mpr hodd
  exact online_zero_pinned_of_sign_bracket hτ.le hc₁ hc₂ hreal₁ hreal₂ hnv₁ hnv₂ hline hreal_seg
    hbracket

end RHTower
