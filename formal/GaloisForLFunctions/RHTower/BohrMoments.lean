/-
The even-moment Bohr tower: every `2k`-th moment is the second moment of a `k`-th power.

The second-moment Bohr transfer (`tendsto_secondMoment_average_steinhaus`) equates the
vertical time average of `‖F‖²` with the Steinhaus-model second moment. Every even moment
reduces to it: `‖F‖^{2k} = ‖Fᵏ‖²`, and a power of a Dirichlet polynomial is again a
Dirichlet polynomial with the (multiplicative) iterated-convolution coefficients.

* `dpolyConv a b s t`, `prodSupport s t` — Dirichlet product coefficients / support.
* `dpoly_mul` — on the line, `dpoly a s · dpoly b t = dpoly (dpolyConv a b s t) (prodSupport s t)`,
  via `e^{-iτ log m}·e^{-iτ log n} = e^{-iτ log(mn)}` grouped fiberwise over `mn`.
* `model_mul` — the same for the model, via multiplicativity `X_{mn} = X_m X_n`.
* `powConv a s k`, `powSupport s k`, `dpoly_pow`, `model_pow` — the `k`-th power as a Dirichlet
  polynomial with iterated-convolution coefficients, by induction on `k`.
* `tendsto_evenMoment_average` / `integral_normPow_dpoly` — both `‖F‖^{2k}` averages equal the
  iterated diagonal `∑ (powConv)²`, by applying the second-moment machinery to `Fᵏ`.
* `tendsto_evenMoment_average_steinhaus` — the general Bohr identity: for every `k` the time
  average of `‖F‖^{2k}` equals the model `2k`-th moment `E‖∑ aₙ Xₙ‖^{2k}`. Taking a power
  commutes with the deterministic-line ↔ character-model correspondence.
-/
import GaloisForLFunctions.RHTower.BohrTransfer

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

/-- Dirichlet-product coefficient: `dpolyConv a b s t k = ∑_{mn=k} aₘ bₙ`. -/
noncomputable def dpolyConv (a b : ℕ → ℝ) (s t : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k), a p.1 * b p.2

/-- Support of a Dirichlet product. -/
def prodSupport (s t : Finset ℕ) : Finset ℕ := (s ×ˢ t).image (fun p => p.1 * p.2)

/-- **The product of two Dirichlet polynomials is a Dirichlet polynomial** with the
convolution coefficients on the product support. -/
theorem dpoly_mul (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, n ≠ 0) (ht : ∀ n ∈ t, n ≠ 0) (τ : ℝ) :
    dpoly a s τ * dpoly b t τ = dpoly (dpolyConv a b s t) (prodSupport s t) τ := by
  rw [dpoly, dpoly, Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ p ∈ s ×ˢ t, p.1 * p.2 ∈ prodSupport s t := fun p hp =>
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p => cterm a τ p.1 * cterm b τ p.2)]
  rw [dpoly]
  apply Finset.sum_congr rfl
  intro k hk
  have hcterm_k : cterm (dpolyConv a b s t) τ k
      = ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k),
          ((a p.1 * b p.2 : ℝ) : ℂ)
            * Complex.exp (-(τ : ℂ) * Complex.I * (Real.log (↑k) : ℂ)) := by
    unfold cterm dpolyConv
    rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [hcterm_k]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, hprod⟩ := hp
  have hlogR : Real.log (↑(p.1 * p.2) : ℝ) = Real.log ↑p.1 + Real.log ↑p.2 := by
    rw [Nat.cast_mul]
    exact Real.log_mul (by exact_mod_cast hs p.1 hp1) (by exact_mod_cast ht p.2 hp2)
  have hexp : Complex.exp (-(τ : ℂ) * Complex.I * (Real.log ↑p.1 : ℂ))
        * Complex.exp (-(τ : ℂ) * Complex.I * (Real.log ↑p.2 : ℂ))
      = Complex.exp (-(τ : ℂ) * Complex.I * (Real.log (↑k) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [show (Real.log (↑k) : ℂ) = (Real.log ↑p.1 : ℂ) + (Real.log ↑p.2 : ℂ) by
          rw [← hprod, hlogR]; push_cast; ring]
    ring
  unfold cterm
  rw [mul_mul_mul_comm, hexp]
  push_cast
  ring

open SteinhausModel

/-- Every element of a product support is `≥ 1`. -/
theorem one_le_of_mem_prodSupport {s t : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n)
    {k : ℕ} (hk : k ∈ prodSupport s t) : 1 ≤ k := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  simp only [Finset.mem_product] at hp
  simpa using Nat.mul_le_mul (hs p.1 hp.1) (ht p.2 hp.2)

/-- **The model version of the Dirichlet product**, via multiplicativity. -/
theorem model_mul (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, n ≠ 0) (ht : ∀ n ∈ t, n ≠ 0) (ω : Omega) :
    (∑ n ∈ s, (a n : ℂ) * X n ω) * (∑ n ∈ t, (b n : ℂ) * X n ω)
      = ∑ k ∈ prodSupport s t, (dpolyConv a b s t k : ℂ) * X k ω := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ p ∈ s ×ˢ t, p.1 * p.2 ∈ prodSupport s t := fun p hp =>
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p => (a p.1 : ℂ) * X p.1 ω * ((b p.2 : ℂ) * X p.2 ω))]
  apply Finset.sum_congr rfl
  intro k hk
  have hxk : (dpolyConv a b s t k : ℂ) * X k ω
      = ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k),
          ((a p.1 * b p.2 : ℝ) : ℂ) * X k ω := by
    unfold dpolyConv
    rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [hxk]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, hprod⟩ := hp
  rw [← hprod, X_mul (hs p.1 hp1) (ht p.2 hp2)]
  push_cast
  ring

/-- Support of the `k`-th power of a Dirichlet polynomial. -/
def powSupport (s : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {1}
  | (k + 1) => prodSupport (powSupport s k) s

/-- Coefficients of the `k`-th power (iterated Dirichlet convolution). -/
noncomputable def powConv (a : ℕ → ℝ) (s : Finset ℕ) : ℕ → ℕ → ℝ
  | 0 => fun j => if j = 1 then 1 else 0
  | (k + 1) => dpolyConv (powConv a s k) a (powSupport s k) s

/-- Every element of a power support is `≥ 1`. -/
theorem one_le_of_mem_powSupport {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ) :
    ∀ j ∈ powSupport s k, 1 ≤ j := by
  induction k with
  | zero =>
    intro j hj
    rw [powSupport] at hj
    simp only [Finset.mem_singleton] at hj
    omega
  | succ k ih =>
    intro j hj
    rw [powSupport] at hj
    exact one_le_of_mem_prodSupport ih hs hj

/-- **The `k`-th power of a Dirichlet polynomial is a Dirichlet polynomial** with the
iterated convolution coefficients. -/
theorem dpoly_pow (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (τ : ℝ) (k : ℕ) :
    dpoly a s τ ^ k = dpoly (powConv a s k) (powSupport s k) τ := by
  induction k with
  | zero =>
    rw [pow_zero, powSupport, powConv, dpoly, Finset.sum_singleton, cterm]
    simp
  | succ k ih =>
    rw [pow_succ, ih, powSupport, powConv]
    exact dpoly_mul (powConv a s k) a (powSupport s k) s
      (fun n hn => Nat.one_le_iff_ne_zero.mp (one_le_of_mem_powSupport hs k n hn))
      (fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)) τ

/-- **The model `k`-th power**, via multiplicativity. -/
theorem model_pow (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (ω : Omega) (k : ℕ) :
    (∑ n ∈ s, (a n : ℂ) * X n ω) ^ k
      = ∑ j ∈ powSupport s k, (powConv a s k j : ℂ) * X j ω := by
  induction k with
  | zero =>
    rw [pow_zero, powSupport, powConv, Finset.sum_singleton]
    simp [X_one]
  | succ k ih =>
    rw [pow_succ, ih, powSupport, powConv]
    exact model_mul (powConv a s k) a (powSupport s k) s
      (fun n hn => Nat.one_le_iff_ne_zero.mp (one_le_of_mem_powSupport hs k n hn))
      (fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)) ω

/-- **`2k`-th moment time average.** The vertical time average of `‖F‖^{2k}` converges to
the iterated diagonal `∑ (powConv)²`, by applying the second-moment mean value to `Fᵏ`. -/
theorem tendsto_evenMoment_average (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ) :
    Tendsto (fun U : ℝ => (∫ t in (0:ℝ)..U, ‖dpoly a s t‖ ^ (2 * k)) / U) atTop
      (𝓝 (∑ j ∈ powSupport s k, powConv a s k j ^ 2)) := by
  have hrw : ∀ t : ℝ,
      ‖dpoly a s t‖ ^ (2 * k) = ‖dpoly (powConv a s k) (powSupport s k) t‖ ^ 2 := by
    intro t
    rw [show 2 * k = k * 2 from by ring, pow_mul, ← norm_pow, dpoly_pow a s hs t k]
  simp_rw [hrw]
  have := tendsto_secondMoment_average (powConv a s k) (powSupport s k) 0
    (one_le_of_mem_powSupport hs k)
  simpa only [zero_add] using this

/-- **`2k`-th moment model identity.** `E‖∑ aₙ Xₙ‖^{2k} = ∑ (powConv)²`. -/
theorem integral_normPow_dpoly (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ) :
    ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * k) ∂steinhausMeasure
      = ∑ j ∈ powSupport s k, powConv a s k j ^ 2 := by
  have hrw : ∀ ω : Omega,
      ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * k)
        = ‖∑ j ∈ powSupport s k, (powConv a s k j : ℂ) * X j ω‖ ^ 2 := by
    intro ω
    rw [show 2 * k = k * 2 from by ring, pow_mul, ← norm_pow, model_pow a s hs ω k]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact integral_normSq_dpoly (powConv a s k) (powSupport s k)
    (fun j hj => Nat.one_le_iff_ne_zero.mp (one_le_of_mem_powSupport hs k j hj))

/-- **The general even-moment Bohr identity.** For every `k`, the vertical time average of
`‖F‖^{2k}` equals the Steinhaus-model `2k`-th moment `E‖∑ aₙ Xₙ‖^{2k}`. Both collapse to the
iterated-convolution diagonal `∑ (powConv)²`: taking a `k`-th power commutes with the
deterministic-line ↔ character-model correspondence, and `‖F‖^{2k} = ‖Fᵏ‖²` reduces every
even moment to the second moment of a power. -/
theorem tendsto_evenMoment_average_steinhaus
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ) :
    Tendsto (fun U : ℝ => (∫ t in (0:ℝ)..U, ‖dpoly a s t‖ ^ (2 * k)) / U) atTop
      (𝓝 (∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * k) ∂steinhausMeasure)) := by
  rw [integral_normPow_dpoly a s hs k]
  exact tendsto_evenMoment_average a s hs k

end RHTower
