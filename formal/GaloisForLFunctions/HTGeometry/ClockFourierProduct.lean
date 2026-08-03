import GaloisForLFunctions.HTGeometry.ClockFourierSynthesis

/-!
# Synthesis turns convolution into multiplication

The coefficient iteration multiplies the potential into the state by convolution. For the
synthesised fields to satisfy the clock equation, convolution has to become ordinary
multiplication:

`∑ₖ (V ⋆ g)ₖ cos kz = (∑ⱼ Vⱼ cos jz)(∑ₘ gₘ cos mz)`.

For cosine series this holds when the coefficients are even, which is no restriction here: evenness
is preserved by convolution and by multiplication by `k²`, so a potential even in the transverse
variable produces an even state at every step, and every quantity stays real.

The proof is the Cauchy product on `ℤ × ℤ`, the product-to-sum identity
`2 cos a cos b = cos(a+b) + cos(a-b)`, the involution `m ↦ -m` which identifies the two halves, and
the shear `(k, j) ↦ (j, k-j)` which folds the result back into a convolution.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Even coefficient sequences -/

/-- A coefficient sequence is even when it is invariant under `k ↦ -k`; equivalently its cosine
series has no sine part. -/
def EvenCoeff (g : ℤ → ℝ) : Prop := ∀ k : ℤ, g (-k) = g k

theorem evenCoeff_sqMul {g : ℤ → ℝ} (hg : EvenCoeff g) : EvenCoeff (sqMul g) := by
  intro k
  rw [sqMul, sqMul, hg k]
  push_cast
  ring

theorem evenCoeff_wienerConv {f g : ℤ → ℝ} (hf : EvenCoeff f) (hg : EvenCoeff g) :
    EvenCoeff (wienerConv f g) := by
  intro k
  rw [wienerConv, wienerConv]
  rw [← (Equiv.neg ℤ).tsum_eq fun j : ℤ => f j * g (-k - j)]
  refine tsum_congr fun j => ?_
  show f (-j) * g (-k - -j) = f j * g (k - j)
  rw [hf j]
  congr 1
  have : (-k - -j) = -(k - j) := by ring
  rw [this, hg (k - j)]

/-! ## Summability on the product -/

theorem summable_prod_of_abs_bound {f g : ℤ → ℝ} (hf : Summable fun j : ℤ => |f j|)
    (hg : Summable fun m : ℤ => |g m|) {F : ℤ × ℤ → ℝ}
    (hF : ∀ p : ℤ × ℤ, |F p| ≤ |f p.1| * |g p.2|) : Summable F := by
  refine Summable.of_abs ?_
  exact (hf.mul_of_nonneg hg (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)).of_nonneg_of_le
    (fun _ => abs_nonneg _) hF

/-! ## The product rule -/

/-- **Synthesis turns convolution into multiplication.** -/
theorem cosSeries_wienerConv {ρ : ℝ} (hρ : 0 ≤ ρ) {f g : ℤ → ℝ}
    (hf : WienerSummable ρ f) (hg : WienerSummable ρ g) (hge : EvenCoeff g) (z : ℝ) :
    cosSeries f z * cosSeries g z = cosSeries (wienerConv f g) z := by
  classical
  have hfa : Summable fun j : ℤ => |f j| := summable_abs_of_wienerSummable hρ hf
  have hga : Summable fun m : ℤ => |g m| := summable_abs_of_wienerSummable hρ hg
  -- the three families on the product
  set C : ℤ × ℤ → ℝ := fun p =>
    (f p.1 * Real.cos ((p.1 : ℝ) * z)) * (g p.2 * Real.cos ((p.2 : ℝ) * z)) with hC
  set P : ℤ × ℤ → ℝ := fun p =>
    f p.1 * g p.2 * Real.cos ((p.1 : ℝ) * z + (p.2 : ℝ) * z) with hP
  set M : ℤ × ℤ → ℝ := fun p =>
    f p.1 * g p.2 * Real.cos ((p.1 : ℝ) * z - (p.2 : ℝ) * z) with hM
  have hbound : ∀ (F : ℤ × ℤ → ℝ),
      (∀ p : ℤ × ℤ, ∃ c : ℝ, |c| ≤ 1 ∧ F p = f p.1 * g p.2 * c) → Summable F := by
    intro F hFrep
    refine summable_prod_of_abs_bound hfa hga fun p => ?_
    obtain ⟨c, hc, hrep⟩ := hFrep p
    rw [hrep, abs_mul, abs_mul]
    have hnn : (0 : ℝ) ≤ |f p.1| * |g p.2| := by positivity
    calc |f p.1| * |g p.2| * |c| ≤ |f p.1| * |g p.2| * 1 :=
          mul_le_mul_of_nonneg_left hc hnn
      _ = |f p.1| * |g p.2| := mul_one _
  have hCs : Summable C := hbound C fun p =>
    ⟨Real.cos ((p.1 : ℝ) * z) * Real.cos ((p.2 : ℝ) * z), by
      rw [abs_mul]
      have h1 : |Real.cos ((p.1 : ℝ) * z)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : |Real.cos ((p.2 : ℝ) * z)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [abs_nonneg (Real.cos ((p.1 : ℝ) * z)), abs_nonneg (Real.cos ((p.2 : ℝ) * z))],
      by rw [hC]; ring⟩
  have hPs : Summable P := hbound P fun p =>
    ⟨Real.cos ((p.1 : ℝ) * z + (p.2 : ℝ) * z), Real.abs_cos_le_one _, by rw [hP]⟩
  have hMs : Summable M := hbound M fun p =>
    ⟨Real.cos ((p.1 : ℝ) * z - (p.2 : ℝ) * z), Real.abs_cos_le_one _, by rw [hM]⟩
  -- the Cauchy product
  have hfn : Summable fun j : ℤ => ‖f j * Real.cos ((j : ℝ) * z)‖ := by
    refine hfa.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.cos ((j : ℝ) * z)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [abs_nonneg (f j), abs_nonneg (Real.cos ((j : ℝ) * z))]
  have hgn : Summable fun m : ℤ => ‖g m * Real.cos ((m : ℝ) * z)‖ := by
    refine hga.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.cos ((m : ℝ) * z)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [abs_nonneg (g m), abs_nonneg (Real.cos ((m : ℝ) * z))]
  have hcauchy : cosSeries f z * cosSeries g z = ∑' p : ℤ × ℤ, C p :=
    tsum_mul_tsum_of_summable_norm hfn hgn
  -- product to sum
  have hsplit : ∀ p : ℤ × ℤ, C p = (P p + M p) / 2 := by
    intro p
    simp only [hC, hP, hM, Real.cos_add, Real.cos_sub]
    ring
  -- the two halves agree, by `m ↦ -m`
  have hflip : (∑' p : ℤ × ℤ, M p) = ∑' p : ℤ × ℤ, P p := by
    rw [← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq M]
    refine tsum_congr fun p => ?_
    show f p.1 * g (-p.2) * Real.cos ((p.1 : ℝ) * z - ((-p.2 : ℤ) : ℝ) * z)
      = f p.1 * g p.2 * Real.cos ((p.1 : ℝ) * z + (p.2 : ℝ) * z)
    rw [hge p.2]
    congr 2
    push_cast
    ring
  have hCP : (∑' p : ℤ × ℤ, C p) = ∑' p : ℤ × ℤ, P p := by
    have : (∑' p : ℤ × ℤ, C p) = (∑' p : ℤ × ℤ, (P p + M p) / 2) := tsum_congr hsplit
    rw [this, tsum_div_const, hPs.tsum_add hMs, hflip]
    ring
  -- the shear folds the sum into a convolution
  let sh : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := by intro q; simp
      right_inv := by intro p; simp }
  have hshear : (∑' p : ℤ × ℤ, P p) = ∑' q : ℤ × ℤ, P (sh q) := (sh.tsum_eq P).symm
  have hPsh : Summable fun q : ℤ × ℤ => P (sh q) := sh.summable_iff.mpr hPs
  have hfold : (∑' q : ℤ × ℤ, P (sh q)) = cosSeries (wienerConv f g) z := by
    rw [hPsh.tsum_prod, cosSeries]
    refine tsum_congr fun k => ?_
    have hrw : ∀ j : ℤ, P (sh (k, j))
        = f j * g (k - j) * Real.cos ((k : ℝ) * z) := by
      intro j
      show f j * g (k - j) * Real.cos ((j : ℝ) * z + ((k - j : ℤ) : ℝ) * z)
        = f j * g (k - j) * Real.cos ((k : ℝ) * z)
      congr 2
      push_cast
      ring
    rw [tsum_congr hrw, tsum_mul_right, wienerConv]
  rw [hcauchy, hCP, hshear, hfold]

end GaloisForLFunctions.HTGeometry
