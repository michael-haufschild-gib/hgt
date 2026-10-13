import GaloisForLFunctions.RHTower.JointAncestryRotationNegativity

/-!
# A rotating coherent model forces a positive proportion of negative phase vectors

Let `D` be a real function on the phase torus `(ℤ/N)^ι`.  Suppose that off a small exceptional
set, `D` at the shifted vector `k + j·1` is within `1` of the model
`L + Re Σ_s b_s exp(g_s · ω̄^j ζ(k))`, where `ζ(k) = s·Z(k)` and `Z(k) = Σ_i a_i ω^{−k_i}` is the
linear phase sum.  If the second moment `V = s² Σ a_i²` is large compared with the radius of the
rotation lemma, then `D < 0` on a fixed proportion of the torus
(`card_neg_ge_of_rotation_model`).

Proof.  Paley–Zygmund puts `|ζ|² ≥ V/2` on `≥ 1/8` of the torus, and Chebyshev puts `|ζ| ≤ R₁`
on all but `1/32` of it.  On the remaining good vectors the rotation lemma gives `≥ cN` negative
shifts.  Orbit counting turns this into `#{D < 0} ≥ (c/16) N^{|ι|}`.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reflecting the sample index: `#{j : Q(ω̄^j)} = #{j : Q(ω^j)}`. -/
theorem card_filter_conj_unitRoot_eq {N : ℕ} [NeZero N] (Q : ℂ → Prop) [DecidablePred Q] :
    ((univ.filter fun j : Fin N => Q (conj (unitRoot N ^ (j : ℕ)))).card) =
      ((univ.filter fun j : Fin N => Q (unitRoot N ^ (j : ℕ))).card) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hneg : ∀ j : Fin N, conj (unitRoot N ^ (((-j : Fin N)) : ℕ)) = unitRoot N ^ (j : ℕ) := by
    intro j
    have hprim := isPrimitiveRoot_unitRoot (N := N) hN.ne'
    have hsum : unitRoot N ^ (((-j : Fin N)) : ℕ) * unitRoot N ^ (j : ℕ) = 1 := by
      rw [← unitRoot_pow_add_fin hN, neg_add_cancel, Fin.val_zero, pow_zero]
    have hw := unitRoot_pow_mul_conj N (j : ℕ)
    have hne : unitRoot N ^ (((-j : Fin N)) : ℕ) ≠ 0 := pow_ne_zero _ (unitRoot_ne_zero N)
    have : unitRoot N ^ (((-j : Fin N)) : ℕ) = conj (unitRoot N ^ (j : ℕ)) := by
      have h1 : unitRoot N ^ (((-j : Fin N)) : ℕ) * unitRoot N ^ (j : ℕ) =
          conj (unitRoot N ^ (j : ℕ)) * unitRoot N ^ (j : ℕ) := by
        rw [hsum, mul_comm, hw]
      exact mul_right_cancel₀ (pow_ne_zero _ (unitRoot_ne_zero N)) h1
    rw [this, Complex.conj_conj]
  refine Finset.card_bij (fun j _ => -j) (fun j hj => ?_) (fun j _ j' _ h => neg_inj.mp h)
    (fun j hj => ⟨-j, ?_, neg_neg j⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [← hneg (-j), neg_neg]; exact hj
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [hneg]; exact hj

/-- **Coherent rotation model ⟹ a positive proportion of negative vectors.** -/
theorem card_neg_ge_of_rotation_model {S : Type*} [Fintype S] {N : ℕ} (hN3 : 3 ≤ N)
    (D : (ι → Fin N) → ℝ) (a : ι → ℝ) {sc : ℝ} (hsc : 0 < sc)
    (g b : S → ℂ) (g₀ : ℂ) (hg : ∀ s, ‖g s‖ = 1) (hg₀ : ‖g₀‖ = 1) {β κ M W₀ : ℝ} (hβ : 0 < β)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hW₀ : 0 ≤ W₀)
    (hB : β ≤ ‖∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s‖)
    (hsep : ∀ s, g s ≠ g₀ → (g s * conj g₀).re ≤ 1 - κ) (hM : ∑ s, ‖b s‖ ≤ M)
    {L : ℝ} (hL : |L| ≤ W₀) {R₁ : ℝ}
    (hVR : 2 * rotRadius β κ M W₀ ^ 2 ≤ sc ^ 2 * ∑ i, a i ^ 2)
    (hR₁ : 32 * (sc ^ 2 * ∑ i, a i ^ 2) ≤ R₁ ^ 2) (hR₁0 : 0 ≤ R₁) (hN : 6 * R₁ + 2 ≤ N)
    (Gerr : Finset (ι → Fin N))
    (hGerr : (31 / 32 : ℝ) * (N : ℝ) ^ Fintype.card ι ≤ Gerr.card)
    (happrox : ∀ k ∈ Gerr, ‖(sc : ℂ) * linearPhaseSum a k‖ ≤ R₁ → ∀ j : Fin N,
      |D (phaseShift j k) - (L + (∑ s, b s * Complex.exp (g s *
        (conj (unitRoot N ^ (j : ℕ)) * ((sc : ℂ) * linearPhaseSum a k)))).re)| ≤ 1) :
    rotFrac κ / 16 * (N : ℝ) ^ Fintype.card ι ≤
      ((univ.filter fun k : ι → Fin N => D k < 0).card : ℝ) := by
  haveI : NeZero N := ⟨by omega⟩
  set V := sc ^ 2 * ∑ i, a i ^ 2 with hV
  set n : ℝ := (N : ℝ) ^ Fintype.card ι with hn
  have hn0 : 0 < n := by positivity
  have hR0 : 0 < rotRadius β κ M W₀ := by
    unfold rotRadius
    have := sin_rotArc_pos hκ hκ1
    have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun s _ => norm_nonneg _) hM
    have h1 : 0 ≤ Real.log (4 * M / β + 1) := Real.log_nonneg (by
      have : 0 ≤ 4 * M / β := by positivity
      linarith)
    have h2 : 0 ≤ Real.log (4 * (W₀ + 1) / β + 1) := Real.log_nonneg (by
      have : 0 ≤ 4 * (W₀ + 1) / β := by positivity
      linarith)
    positivity
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVR
  have ha2 : 0 < ∑ i, a i ^ 2 := by
    by_contra h; push Not at h
    have : V ≤ 0 := by rw [hV]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
    linarith
  have hR₁pos : 0 < R₁ := by
    rcases hR₁0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hR₁; nlinarith
  -- Paley–Zygmund and Chebyshev
  set A := univ.filter fun k : ι → Fin N => (∑ i, a i ^ 2) / 2 ≤ ‖linearPhaseSum a k‖ ^ 2
  set C := univ.filter fun k : ι → Fin N => (R₁ / sc) ^ 2 < ‖linearPhaseSum a k‖ ^ 2
  have hA : n / 8 ≤ (A.card : ℝ) := card_half_le_normSq_linearPhaseSum hN3 a ha2
  have hC : (C.card : ℝ) ≤ n / 32 := by
    have h := card_lt_normSq_linearPhaseSum_le (ι := ι) hN3 a (R := R₁ / sc) (by positivity)
    refine h.trans ?_
    rw [div_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : n * (∑ i, a i ^ 2) * sc ^ 2 * 32 ≤ n * R₁ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hR₁ hn0.le
      nlinarith
    linarith
  -- the good set
  set G := (Gerr ∩ A) \ C
  have hG : n / 16 ≤ (G.card : ℝ) := by
    have h1 : ((Gerr ∩ A).card : ℝ) ≥ (A.card : ℝ) - (n - Gerr.card) := by
      have hu : (Gerr ∪ A).card ≤ (univ : Finset (ι → Fin N)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      have hia := Finset.card_union_add_card_inter Gerr A
      have huniv : ((univ : Finset (ι → Fin N)).card : ℝ) = n := by
        simp [hn]
      have : ((Gerr ∪ A).card : ℝ) ≤ n := by rw [← huniv]; exact_mod_cast hu
      have hia' : ((Gerr ∪ A).card : ℝ) + (Gerr ∩ A).card = Gerr.card + A.card := by
        exact_mod_cast hia
      linarith
    have h2 : ((G.card : ℕ) : ℝ) ≥ ((Gerr ∩ A).card : ℝ) - C.card := by
      have := Finset.card_sdiff_add_card_inter (Gerr ∩ A) C
      have hle : ((Gerr ∩ A) ∩ C).card ≤ C.card := Finset.card_le_card Finset.inter_subset_right
      have : ((G.card : ℕ) : ℝ) + ((Gerr ∩ A) ∩ C).card = (Gerr ∩ A).card := by
        exact_mod_cast this
      have : (((Gerr ∩ A) ∩ C).card : ℝ) ≤ C.card := by exact_mod_cast hle
      linarith
    linarith
  -- each good vector has many negative shifts
  have hshift : ∀ k ∈ G, rotFrac κ * N ≤
      ((univ.filter fun j : Fin N => D (phaseShift j k) < 0).card : ℝ) := by
    intro k hk
    have hkG : k ∈ Gerr := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hk).1).1
    have hkA : k ∈ A := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hk).1).2
    have hkC : k ∉ C := (Finset.mem_sdiff.mp hk).2
    set ζ := (sc : ℂ) * linearPhaseSum a k with hζ
    have hnζ : ‖ζ‖ = sc * ‖linearPhaseSum a k‖ := by
      rw [hζ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsc]
    have hζ1 : ‖ζ‖ ≤ R₁ := by
      have h := (Finset.mem_filter.not.mp hkC)
      simp only [Finset.mem_univ, true_and, not_lt] at h
      rw [hnζ]
      have h' : ‖linearPhaseSum a k‖ ≤ R₁ / sc :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
      rw [le_div_iff₀ hsc] at h'
      linarith
    have hζ0 : rotRadius β κ M W₀ ≤ ‖ζ‖ := by
      have h := (Finset.mem_filter.mp hkA).2
      have hsq : rotRadius β κ M W₀ ^ 2 ≤ ‖ζ‖ ^ 2 := by
        rw [hnζ, mul_pow]
        have := mul_le_mul_of_nonneg_left h (sq_nonneg sc)
        nlinarith
      nlinarith [norm_nonneg ζ, sq_nonneg (‖ζ‖ - rotRadius β κ M W₀)]
    set e : Fin N → ℝ := fun j => D (phaseShift (-j) k) -
      (L + (∑ s, b s * Complex.exp (g s * (unitRoot N ^ (j : ℕ) * ζ))).re) with he
    have hconjneg : ∀ j : Fin N, conj (unitRoot N ^ (((-j : Fin N)) : ℕ)) =
        unitRoot N ^ (j : ℕ) := by
      intro j
      have hN : 0 < N := by omega
      have hsum : unitRoot N ^ (((-j : Fin N)) : ℕ) * unitRoot N ^ (j : ℕ) = 1 := by
        rw [← unitRoot_pow_add_fin hN, neg_add_cancel, Fin.val_zero, pow_zero]
      have hw := unitRoot_pow_mul_conj N (j : ℕ)
      have : unitRoot N ^ (((-j : Fin N)) : ℕ) = conj (unitRoot N ^ (j : ℕ)) := by
        have h1 : unitRoot N ^ (((-j : Fin N)) : ℕ) * unitRoot N ^ (j : ℕ) =
            conj (unitRoot N ^ (j : ℕ)) * unitRoot N ^ (j : ℕ) := by
          rw [hsum, mul_comm, hw]
        exact mul_right_cancel₀ (pow_ne_zero _ (unitRoot_ne_zero N)) h1
      rw [this, Complex.conj_conj]
    have he1 : ∀ j, |e j| ≤ 1 := by
      intro j
      have := happrox k hkG hζ1 (-j)
      rw [hconjneg j] at this
      exact this
    have hrot := card_rotation_negative g b g₀ hg hg₀ hβ hκ hκ1 hW₀ hB hsep hM hN hζ0 hζ1 hL e he1
    have hsub : (univ.filter fun j : Fin N =>
        L + (∑ s, b s * Complex.exp (g s * (unitRoot N ^ (j : ℕ) * ζ))).re + e j < 0).image
          (fun j => -j) ⊆ univ.filter fun j : Fin N => D (phaseShift j k) < 0 := by
      intro j hj
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
      simp only [he] at hj'
      linarith
    have hinj : Set.InjOn (fun j : Fin N => -j) ↑(univ.filter fun j : Fin N =>
        L + (∑ s, b s * Complex.exp (g s * (unitRoot N ^ (j : ℕ) * ζ))).re + e j < 0) :=
      fun j _ j' _ h => neg_inj.mp h
    calc rotFrac κ * N ≤ _ := hrot
      _ = (((univ.filter fun j : Fin N =>
          L + (∑ s, b s * Complex.exp (g s * (unitRoot N ^ (j : ℕ) * ζ))).re + e j < 0).image
            (fun j => -j)).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub
  -- orbit counting
  have horbit := card_filter_mul_eq_sum_card_shift (ι := ι) (N := N) (fun k => D k < 0)
  have hsumG : (G.card : ℝ) * (rotFrac κ * N) ≤
      ∑ k : ι → Fin N, ((univ.filter fun j : Fin N => D (phaseShift j k) < 0).card : ℝ) := by
    calc (G.card : ℝ) * (rotFrac κ * N) = ∑ _k ∈ G, rotFrac κ * N := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ G, ((univ.filter fun j : Fin N => D (phaseShift j k) < 0).card : ℝ) :=
          Finset.sum_le_sum hshift
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.cast_nonneg _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hfrac := rotFrac_pos hκ hκ1
  have : rotFrac κ / 16 * n * N ≤ ((univ.filter fun k : ι → Fin N => D k < 0).card : ℝ) * N := by
    rw [horbit]
    refine le_trans ?_ hsumG
    have := mul_le_mul_of_nonneg_right hG (by positivity : (0 : ℝ) ≤ rotFrac κ * N)
    nlinarith
  exact le_of_mul_le_mul_right this hNpos

end

end RHTower
