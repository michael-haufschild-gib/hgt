import GaloisForLFunctions.HTGeometry.PositiveSquareRootBoundaryBlowup
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

open Complex Filter Topology
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A meromorphic germ with a finite nonzero limit along any punctured path has order zero. -/
lemma meromorphicOrderAt_eq_zero_of_path_tendsto_ne_zero
    {A : Type*} {l : Filter A} [l.NeBot]
    {f : ℂ → ℂ} {p c : ℂ} {path : A → ℂ}
    (hc : c ≠ 0)
    (hpath : Tendsto path l (nhdsWithin p {p}ᶜ))
    (hlim : Tendsto (fun a => f (path a)) l (nhds c)) :
    meromorphicOrderAt f p = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hcob := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    have htop : Tendsto (fun a => ‖f (path a)‖) l atTop :=
      tendsto_norm_atTop_iff_cobounded.mpr (hcob.comp hpath)
    exact (not_tendsto_atTop_of_tendsto_nhds hlim.norm) htop
  · have hzero := tendsto_zero_of_meromorphicOrderAt_pos hpos
    have hczero : c = 0 := tendsto_nhds_unique hlim (hzero.comp hpath)
    exact hc hczero

/-- A finite positive square-root boundary law cannot be the real radial restriction of a
single-valued meromorphic germ.  Squaring the boundary law makes the obstruction parity-exact:
`(z-p) f(z)^(2 : ℕ)` would have order both zero and `1 + 2 ord_p(f)`. -/
theorem false_of_meromorphicAt_of_positive_sqrt_scaled_boundary
    {S : ℝ → ℝ} {f : ℂ → ℂ} {B C : ℝ}
    (hB : 0 < B) (hC : 0 < C)
    (hf : MeromorphicAt f (1 / B ^ (2 : ℕ) : ℝ))
    (hagree : (fun t : ℝ => f t) =ᶠ[
      nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ)))]
      (fun t : ℝ => (S t : ℂ)))
    (hboundary : Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) * S t)
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ)))) (nhds C)) :
    False := by
  let p : ℝ := 1 / B ^ (2 : ℕ)
  let l : Filter ℝ := nhdsWithin p (Set.Ico 0 p)
  let F : ℂ → ℂ := fun z => (z - p) * f z ^ (2 : ℕ)
  let c : ℂ := (-(C ^ (2 : ℕ) / B ^ (2 : ℕ)) : ℝ)
  have hBsq : 0 < B ^ (2 : ℕ) := sq_pos_of_pos hB
  have hp : 0 < p := one_div_pos.mpr hBsq
  letI : l.NeBot := (isLUB_Ico hp).nhdsWithin_neBot (Set.nonempty_Ico.2 hp)
  have hreal : Tendsto (fun t : ℝ => (t - p) * S t ^ (2 : ℕ)) l
      (nhds (-(C ^ (2 : ℕ) / B ^ (2 : ℕ)))) := by
    have hsquare := hboundary.pow 2
    have hscaled := hsquare.const_mul (-(1 / B ^ (2 : ℕ)))
    have heq :
        (fun t : ℝ => -(1 / B ^ (2 : ℕ)) *
          (Real.sqrt (1 - B ^ (2 : ℕ) * t) * S t) ^ (2 : ℕ)) =ᶠ[
            nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ)))]
        (fun t : ℝ => (t - 1 / B ^ (2 : ℕ)) * S t ^ (2 : ℕ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hdelta : 0 ≤ 1 - B ^ (2 : ℕ) * t := by
        have := (lt_div_iff₀ hBsq).1 ht.2
        exact sub_nonneg.mpr (by simpa only [mul_comm] using this.le)
      rw [mul_pow, Real.sq_sqrt hdelta]
      field_simp [hBsq.ne']
      ring
    have htarget := hscaled.congr' heq
    dsimp only [p, l]
    convert htarget using 1
    ring
  have hpath : Tendsto (fun t : ℝ => (t : ℂ)) l
      (nhdsWithin (p : ℂ) ({(p : ℂ)}ᶜ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]
      exact ne_of_lt ht.2
  have hcomplex : Tendsto
      (fun t : ℝ => Complex.ofReal ((t - p) * S t ^ (2 : ℕ))) l
      (nhds c) :=
    (Complex.continuous_ofReal.tendsto _).comp hreal
  have hFlim : Tendsto (fun t : ℝ => F t) l
      (nhds c) := by
    apply hcomplex.congr'
    filter_upwards [hagree] with t ht
    dsimp only [F]
    rw [ht]
    push_cast
    rfl
  have hlin : MeromorphicAt (fun z : ℂ => z - (p : ℂ)) p := by fun_prop
  have hF : MeromorphicAt F p := by
    simpa only [F, Pi.mul_apply, Pi.pow_apply] using! hlin.mul (hf.pow 2)
  have hlimit_ne : c ≠ 0 := by
    dsimp only [c]
    exact Complex.ofReal_ne_zero.mpr
      (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hC.ne') (pow_ne_zero 2 hB.ne')))
  have horderF : meromorphicOrderAt F p = 0 :=
    meromorphicOrderAt_eq_zero_of_path_tendsto_ne_zero hlimit_ne hpath hFlim
  have hFeq : F = (fun z : ℂ => z - (p : ℂ)) * f ^ (2 : ℕ) := by
    funext z
    simp only [F, Pi.mul_apply, Pi.pow_apply]
  rw [hFeq] at horderF
  rw [meromorphicOrderAt_mul hlin (hf.pow 2), meromorphicOrderAt_id_sub_const,
    meromorphicOrderAt_pow hf] at horderF
  have hfinite : meromorphicOrderAt f p ≠ ⊤ := by
    intro htop
    rw [htop] at horderF
    simp at horderF
  lift meromorphicOrderAt f p to ℤ using hfinite with k hk
  rw [← hk] at horderF
  change ((1 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ) *
      (k : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) at horderF
  have hparity : (1 : ℤ) + 2 * k = 0 := by exact_mod_cast horderF
  omega

end

end GaloisForLFunctions.HTGeometry
