import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.WindowEnergy

/-! # Saturated block amplitudes with drifting harmonic tolerances -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

theorem order_mul_retention (r : ℕ+) (δ : ℝ) :
    (r.val:ℝ)*retentionCeiling r δ = 1+((r.val:ℝ)-1)*δ := by
  unfold retentionCeiling
  field_simp [show (r.val:ℝ) ≠ 0 by exact_mod_cast r.ne_zero]
  ring

/-- Saturation leaves no Fejér energy outside an exhaustion of the retained mass.
Every block of r consecutive harmonics consequently has the same limit. -/
theorem saturated_block_limit {r : ℕ+} {t d : ℕ → ℝ} {δ : ℝ} {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 δ))
    (hc : ∀ j, harmonicTest r (d j) (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hs : HasSum m (retentionCeiling r δ)) (k : ℕ) :
    Tendsto (fun j => blockReading (v j) (t j) k r.val) atTop (𝓝 ((r.val:ℂ)*(retentionCeiling r δ:ℝ))) := by
  let q := retentionCeiling r δ
  let cap (j : ℕ) := (r.val:ℝ)+(r.val:ℝ)*((r.val:ℝ)-1)*d j
  have hcap : Tendsto cap atTop (𝓝 ((r.val:ℝ)^2*q)) := by
    rw [show (r.val:ℝ)^2*q = _ from retentionCeiling_mul_sq r δ]
    exact (hd.const_mul ((r.val:ℝ)*((r.val:ℝ)-1))).const_add _
  have net : Tendsto (fun F : Finset ℕ+ => ∑ n ∈ F, m n) atTop (𝓝 q) := hs
  have amp := (net.const_mul (r.val:ℝ)).ofReal
  simp only [Complex.ofReal_mul,Complex.ofReal_natCast] at amp
  have ene := (net.const_mul ((r.val:ℝ)^2)).const_sub ((r.val:ℝ)^2*q)
  rw [sub_self] at ene
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/3 := by positivity
  obtain ⟨F,hF,hE⟩ := ((Metric.tendsto_nhds.mp amp (ε/3) he).and
    (ene.eventually_lt_const (sq_pos_of_pos he))).exists
  have ha := windowBlock_limit ht hm F k r.val
  have htail := hcap.sub (windowFejer_limit ht hm F r.val)
  filter_upwards [Metric.tendsto_nhds.mp ha (ε/3) he,htail.eventually_lt_const hE] with j hj hQ
  let B := blockReading (v j) (t j) k r.val
  let A := windowBlock (v j) (t j) F k r.val
  have hb := windowBlock_tail_sq (v j) (t j) F k r.val
  have hpos := sub_nonneg.mpr (windowFejer_le (v j) (t j) F r.val)
  have hfe : fejerReading (v j) (t j) r.val ≤ cap j := fejer_bound (hc j) _ le_rfl
  have hsq : ‖B-A‖^2 < (ε/3)^2 :=
    (hb.trans (mul_le_of_le_one_left hpos (sub_le_self _ (windowMass_nonneg _ _)))).trans_lt
      ((sub_le_sub_right hfe _).trans_lt hQ)
  have hBA : dist B A < ε/3 := by
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) he.le).mp hsq
  let C := (r.val:ℂ)*(q:ℂ)
  have h₁ := dist_triangle B A C
  have h₂ := dist_triangle A ((r.val:ℂ)*(∑ n ∈ F, m n:ℝ)) C
  change dist B C < ε
  linarith only [h₁,h₂,hBA,hj,hF]

theorem adjacent_block_difference (v : MissingWave) (t : ℝ) (k d : ℕ) :
    harmonicReading v t (k+d)-harmonicReading v t k = blockReading v t (k+1) d-blockReading v t k d := by
  have h := Finset.sum_range_succ' (fun i => harmonicReading v t (k+i)) d
  rw [Finset.sum_range_succ] at h
  simp only [Nat.add_zero] at h
  have he : (∑ i ∈ Finset.range d, harmonicReading v t (k+(i+1))) = blockReading v t (k+1) d := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (harmonicReading v t) (by omega)
  rw [he] at h
  change blockReading v t k d+_ = _ at h
  linear_combination h

#print axioms order_mul_retention
#print axioms saturated_block_limit
#print axioms adjacent_block_difference

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
