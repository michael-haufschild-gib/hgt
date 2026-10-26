import GaloisForLFunctions.MultiplicativePositivityGeometry.SummableBochner
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Twisting is convolution; primes in one progression realize the summable cone

* **Convolution law** (`IsBoundaryDivisor.twist_bohr`). Twisting the weights of any boundary datum
  with divisor `D` by the Bohr series `B(t) = Σ_γ φ(γ) cos(t h(γ))` of an absolutely summable
  even positive-definite `φ` (heights `h : Γ →+ ℝ`) gives the boundary divisor
  `(φ ∗_h D)(u) = Σ_γ φ(γ) D(u − h(γ))`. The twisted trace is the `φ`-average of shifted traces of
  the base, and Tannery's theorem passes to the boundary.
* **`δ₀`-bases are universal** (`delta_base_realizes`). A base with divisor `δ₀` realizes every
  pushforward of an absolutely summable positive-definite function.
* **Primes in a progression** (`class_isBoundaryDivisor`, `progression_realizes`). For `a` a unit
  mod `q`, the weights `φ(q) Λ(n) 1_{n ≡ a} n^{−1−x}` have divisor `δ₀`: the `L`-series of `Λ` on the
  class is `φ(q)⁻¹/(s − 1)` plus a function continuous on `Re s ≥ 1` (Dirichlet's theorem in
  Mathlib's form). So the primes of a single residue class already realize every absolutely
  summable positive-definite configuration: the boundary content of multiplicative positivity does
  not depend on which progression carries the primes.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### The convolution law -/

section Convolution

variable {Γ : Type*} [AddCommGroup Γ] {ι : Type*}

/-- A cosine trace of nonnegative weights is largest at `0`. -/
theorem abs_cosineTrace_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (lam : ι → ℝ)
    (u : ℝ) : |cosineTrace w lam u| ≤ cosineTrace w lam 0 := by
  unfold cosineTrace
  simp only [mul_zero, Real.cos_zero, mul_one]
  have ht := summable_cosineTrace_terms hw hs lam u
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm ht.norm).trans (Summable.tsum_le_tsum (fun i => ?_) ht.norm hs)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
  exact mul_le_of_le_one_right (hw i) (Real.abs_cos_le_one _)

/-- Base weights twisted by the Bohr series of `φ` at their frequencies. -/
noncomputable def twistByBohr (b : ℝ → ι → ℝ) (lam : ι → ℝ) (φ : Γ → ℝ) (h : Γ →+ ℝ) (x : ℝ)
    (i : ι) : ℝ :=
  b x i * bohrSeries φ h (lam i)

/-- The twisted trace is the `φ`-average of shifted base traces. -/
theorem trace_twistByBohr {b : ℝ → ι → ℝ} {lam : ι → ℝ} {x : ℝ} (hb0 : ∀ i, 0 ≤ b x i)
    (hbs : Summable (b x)) {φ : Γ → ℝ} (hs : Summable φ) (h : Γ →+ ℝ) (u : ℝ) :
    cosineTrace (twistByBohr b lam φ h x) lam u = ∑' γ, φ γ *
      ((cosineTrace (b x) lam (u - h γ) + cosineTrace (b x) lam (u + h γ)) / 2) := by
  set f : ι → Γ → ℝ := fun i γ => b x i * (φ γ * Real.cos (lam i * h γ)) * Real.cos (lam i * u)
  have hf : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded (Summable.mul_of_nonneg hbs hs.abs hb0 fun γ => abs_nonneg _)
      fun p => ?_
    obtain ⟨i, γ⟩ := p
    simp only [Function.uncurry_apply_pair, f, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 i)]
    have h1 := Real.abs_cos_le_one (lam i * h γ)
    have h2 := Real.abs_cos_le_one (lam i * u)
    have h3 := abs_nonneg (φ γ)
    calc b x i * (|φ γ| * |Real.cos (lam i * h γ)|) * |Real.cos (lam i * u)| ≤
          b x i * (|φ γ| * 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) (hb0 i)) h2
            (abs_nonneg _) (mul_nonneg (hb0 i) (by linarith))
      _ = _ := by ring
  have hrow : ∀ i, HasSum (f i) (b x i * bohrSeries φ h (lam i) * Real.cos (lam i * u)) :=
    fun i => by
      have hB : Summable fun γ => φ γ * Real.cos (lam i * h γ) :=
        Summable.of_norm_bounded hs.abs fun γ => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      exact (hB.hasSum.mul_left (b x i)).mul_right _
  have hcol : ∀ γ, ∑' i, f i γ = φ γ *
      ((cosineTrace (b x) lam (u - h γ) + cosineTrace (b x) lam (u + h γ)) / 2) := fun γ => by
    have hA := summable_cosineTrace_terms hb0 hbs lam (u - h γ)
    have hB := summable_cosineTrace_terms hb0 hbs lam (u + h γ)
    unfold cosineTrace
    rw [← Summable.tsum_add hA hB, ← tsum_div_const, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    simp only [f]
    rw [show lam i * (u - h γ) = lam i * u - lam i * h γ by ring,
      show lam i * (u + h γ) = lam i * u + lam i * h γ by ring, Real.cos_sub, Real.cos_add]
    ring
  unfold cosineTrace twistByBohr
  calc ∑' i, b x i * bohrSeries φ h (lam i) * Real.cos (lam i * u) = ∑' i, ∑' γ, f i γ :=
        tsum_congr fun i => (hrow i).tsum_eq.symm
    _ = ∑' γ, ∑' i, f i γ := hf.tsum_comm.symm
    _ = _ := tsum_congr hcol

/-- **The convolution law.** Twisting a boundary datum with divisor `D` by the Bohr series of an
absolutely summable even positive-definite `φ` gives the divisor `u ↦ Σ_γ φ(γ) D(u − h(γ))`. -/
theorem IsBoundaryDivisor.twist_bohr {lam : ι → ℝ} {b : ℝ → ι → ℝ} {D : ℝ → ℝ}
    (hb : IsBoundaryDivisor lam b D) {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hs : Summable φ)
    (h : Γ →+ ℝ) :
    IsBoundaryDivisor lam (twistByBohr b lam φ h) fun u => ∑' γ, φ γ * D (u - h γ) where
  nonneg x hx i := mul_nonneg (hb.nonneg x hx i) (bohrSeries_nonneg hφ hs h _)
  summable x hx := Summable.of_nonneg_of_le
    (fun i => mul_nonneg (hb.nonneg x hx i) (bohrSeries_nonneg hφ hs h _))
    (fun i => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_bohrSeries_le hs h _))
      (hb.nonneg x hx i))
    ((hb.summable x hx).mul_right _)
  tendsto u := by
    have hD := hb.isEvenPosDef
    have hD0 := hD.apply_zero_nonneg
    have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x * cosineTrace (b x) lam 0 ≤ D 0 + 1 :=
      (eventually_mem_nhdsWithin.mono fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => (hx : 0 < x)).and
        ((hb.tendsto 0).eventually (ge_mem_nhds (by linarith)))
    have hbd : ∀ x, 0 < x → x * cosineTrace (b x) lam 0 ≤ D 0 + 1 →
        ∀ v, |x * cosineTrace (b x) lam v| ≤ D 0 + 1 := fun x hx h1 v => by
      rw [abs_mul, abs_of_pos hx]
      exact (mul_le_mul_of_nonneg_left
        (abs_cosineTrace_le (hb.nonneg x hx) (hb.summable x hx) lam v) hx.le).trans h1
    have hT := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun x γ => φ γ * ((x * cosineTrace (b x) lam (u - h γ) +
        x * cosineTrace (b x) lam (u + h γ)) / 2))
      (g := fun γ => φ γ * ((D (u - h γ) + D (u + h γ)) / 2))
      (bound := fun γ => (D 0 + 1) * |φ γ|) (hs.abs.mul_left _)
      (fun γ => (((hb.tendsto _).add (hb.tendsto _)).div_const 2).const_mul (φ γ))
      (hev.mono fun x hx γ => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [abs_div, abs_two]
        have h1 := hbd x hx.1 hx.2 (u - h γ)
        have h2 := hbd x hx.1 hx.2 (u + h γ)
        have := abs_add_le (x * cosineTrace (b x) lam (u - h γ))
          (x * cosineTrace (b x) lam (u + h γ))
        linarith)
    -- Reflect the `u + h γ` half.
    have hDb : ∀ v, |D v| ≤ D 0 := hD.abs_le_apply_zero
    have hg1 : Summable fun γ => φ γ * D (u - h γ) :=
      Summable.of_norm_bounded (hs.abs.mul_right (D 0)) fun γ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)
    have hg2 : Summable fun γ => φ γ * D (u + h γ) :=
      Summable.of_norm_bounded (hs.abs.mul_right (D 0)) fun γ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)
    have href : ∑' γ, φ γ * D (u + h γ) = ∑' γ, φ γ * D (u - h γ) := by
      rw [← (Equiv.neg Γ).tsum_eq]
      exact tsum_congr fun γ => by simp [hφ.even, sub_eq_add_neg]
    have hlimval : ∑' γ, φ γ * ((D (u - h γ) + D (u + h γ)) / 2) = ∑' γ, φ γ * D (u - h γ) := by
      rw [show (fun γ => φ γ * ((D (u - h γ) + D (u + h γ)) / 2)) =
        fun γ => (φ γ * D (u - h γ) + φ γ * D (u + h γ)) / 2 from funext fun γ => by ring,
        tsum_div_const, Summable.tsum_add hg1 hg2, href]
      ring
    rw [hlimval] at hT
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [trace_twistByBohr (hb.nonneg x hx) (hb.summable x hx) hs h u, ← tsum_mul_left]
    exact tsum_congr fun γ => by ring

/-- **`δ₀`-bases are universal.** A base datum with divisor `δ₀` realizes the pushforward of every
absolutely summable even positive-definite function. -/
theorem delta_base_realizes {lam : ι → ℝ} {b : ℝ → ι → ℝ}
    (hb : IsBoundaryDivisor lam b fun u => if u = 0 then 1 else 0) {φ : Γ → ℝ}
    (hφ : IsEvenPosDef φ) (hs : Summable φ) (h : Γ →+ ℝ) :
    IsBoundaryDivisor lam (twistByBohr b lam φ h) (pushDivisor φ h) :=
  hb.twist_bohr hφ hs h

end Convolution

/-! ### Primes in one residue class -/

section Progression

open ArithmeticFunction ArithmeticFunction.vonMangoldt

open scoped LSeries.notation

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- Weights `φ(q) Λ(n) 1_{n ≡ a} n^{−1−x}`. -/
noncomputable def classWeight (q : ℕ) (a : ZMod q) (x : ℝ) (n : ℕ) : ℝ :=
  q.totient * residueClass a n * (n : ℝ) ^ (-(1 + x))

omit [NeZero q] in
theorem classWeight_nonneg (x : ℝ) (n : ℕ) : 0 ≤ classWeight q a x n :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (residueClass_nonneg a n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

omit [NeZero q] in
theorem classWeight_le (x : ℝ) (n : ℕ) : classWeight q a x n ≤ q.totient * zetaBoundaryWeight x n := by
  unfold classWeight zetaBoundaryWeight
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (residueClass_le a n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (Nat.cast_nonneg _)

omit [NeZero q] in
theorem re_term_residueClass (σ u : ℝ) (n : ℕ) :
    (LSeries.term (fun n => (residueClass a n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) n).re =
      residueClass a n * (n : ℝ) ^ (-σ) * Real.cos (logFrequency n * u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg, Complex.mul_re,
      RHTower.re_natCast_cpow_neg hn σ u, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, logFrequency, mul_comm (Real.log n) u]
    ring

/-- **Primes in one residue class form a boundary datum with divisor `δ₀`.** -/
theorem class_isBoundaryDivisor (ha : IsUnit a) :
    IsBoundaryDivisor logFrequency (classWeight q a) fun u => if u = 0 then 1 else 0 where
  nonneg x _ n := classWeight_nonneg x n
  summable x hx := Summable.of_nonneg_of_le (classWeight_nonneg x) (classWeight_le x)
    ((summable_zetaBoundaryWeight hx).mul_left _)
  tendsto u := by
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    set s : ℝ → ℂ := fun x => ((1 + x : ℝ) : ℂ) + (u : ℂ) * I
    -- The trace is `φ(q) Re L(s)` and `L(s) = Aux(s) + φ(q)⁻¹/(s − 1)`.
    have htrace : ∀ x, 0 < x → x * cosineTrace (classWeight q a x) logFrequency u =
        q.totient * (x * (LFunctionResidueClassAux a (s x)).re) + x * x / (x ^ 2 + u ^ 2) := by
      intro x hx
      have hre : 1 < (s x).re := by simp [s]; linarith
      have hS : LSeriesSummable (fun n => (residueClass a n : ℂ)) (s x) := by
        refine Summable.of_norm_bounded
          (summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hre))
          fun n => LSeries.norm_term_le _ ?_
        rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (residueClass_nonneg a n), abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact residueClass_le a n
      have hL := eqOn_LFunctionResidueClassAux ha (show s x ∈ {s : ℂ | 1 < s.re} from hre)
      have hcos : cosineTrace (classWeight q a x) logFrequency u =
          q.totient * (LSeries (fun n => (residueClass a n : ℂ)) (s x)).re := by
        unfold cosineTrace
        rw [LSeries, Complex.re_tsum hS, ← tsum_mul_left]
        refine tsum_congr fun n => ?_
        simp only [s]
        rw [re_term_residueClass, classWeight]
        ring
      rw [hcos, hL]
      have hs1 : s x - 1 = (x : ℂ) + (u : ℂ) * I := by simp [s]; ring
      rw [Complex.sub_re, hs1]
      have hden : (x : ℂ) + (u : ℂ) * I ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
        linarith
      have hre2 : ((q.totient : ℂ)⁻¹ / ((x : ℂ) + (u : ℂ) * I)).re =
          (q.totient : ℝ)⁻¹ * (x / (x ^ 2 + u ^ 2)) := by
        have e1 : ((q.totient : ℂ))⁻¹ = (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [e1, div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, Complex.add_im, Complex.mul_im]
        ring
      rw [hre2]
      field_simp
      ring
    -- The continuous part vanishes after multiplying by `x`; the pole gives `δ₀`.
    have hcont : ContinuousWithinAt (LFunctionResidueClassAux a) {z : ℂ | 1 ≤ z.re}
        (1 + (u : ℂ) * I) :=
      continuousOn_LFunctionResidueClassAux a _ (by simp)
    have hsx : Tendsto s (𝓝[>] 0) (𝓝[{z : ℂ | 1 ≤ z.re}] (1 + (u : ℂ) * I)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous s := by fun_prop
        have h := this.continuousAt (x := 0) |>.tendsto
        simpa [s] using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        show 1 ≤ (s x).re
        simp [s]
        exact (Set.mem_Ioi.mp hx).le
    have hAux : Tendsto (fun x => x * (LFunctionResidueClassAux a (s x)).re) (𝓝[>] 0) (𝓝 0) := by
      have h1 := (Complex.continuous_re.tendsto _).comp (hcont.tendsto.comp hsx)
      have h2 := ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).mul h1
      simpa using h2
    have hpole : Tendsto (fun x : ℝ => x * x / (x ^ 2 + u ^ 2)) (𝓝[>] 0)
        (𝓝 (if u = 0 then 1 else 0)) := by
      split_ifs with hu
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hx0 : 0 < x := hx
        rw [hu, eq_comm, div_eq_one_iff_eq (ne_of_gt (by simpa using pow_pos hx0 2))]
        ring
      · have hc : ContinuousAt (fun x : ℝ => x * x / (x ^ 2 + u ^ 2)) 0 :=
          (continuous_id.mul continuous_id).continuousAt.div (by fun_prop)
            (by positivity)
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have := (hAux.const_mul (q.totient : ℝ)).add hpole
    rw [mul_zero, zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (htrace x hx).symm

/-- **Primes in one progression realize the summable cone.** For `a` a unit mod `q` and every
absolutely summable even positive-definite `φ` with heights `h`, the class weights twisted by the
Bohr series of `φ` have boundary divisor `D_h(u) = Σ_{h(γ) = u} φ(γ)`. -/
theorem progression_realizes {Γ : Type*} [AddCommGroup Γ] (ha : IsUnit a) {φ : Γ → ℝ}
    (hφ : IsEvenPosDef φ) (hs : Summable φ) (h : Γ →+ ℝ) :
    IsBoundaryDivisor logFrequency (twistByBohr (classWeight q a) logFrequency φ h)
      (pushDivisor φ h) :=
  delta_base_realizes (class_isBoundaryDivisor ha) hφ hs h

end Progression

end GaloisForLFunctions.MultiplicativePositivityGeometry
