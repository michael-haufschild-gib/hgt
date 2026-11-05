import GaloisForLFunctions.Core
import GaloisForLFunctions.HTGeometry.KroneckerApproxRecurrence
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Consistent tangencies force near-coincidences

The converse of `ConsistentTangenciesAreTheOnlySourceOfNearCoincidences`. Let `D(s) = G(p_i^{−s})`
be a finite-prime carrier whose translates `s ↦ G(v_i p_i^{−s})` are holomorphic for every `v`, and
let `x_i = u_i p_i^{−σ*}`, `|u_i| = 1`, be a consistent point of its Bohr lift at which
`f(w) = G(u_i p_i^{−(σ* + w)})` has an isolated zero of order `m ≥ 2` at `w = 0` (a consistent
tangency).

* **Near-coincidences at every scale** (`exists_zeros_near_tangency`). For every `δ > 0` and every
  `T₀` there is `t > T₀` such that `w ↦ D(σ* + it + w)` has zeros in `|w| < δ` of total
  multiplicity `m ≥ 2`. Kronecker's theorem for the `ℚ`-independent prime logarithms
  (`kronecker_approx_atTop`, `linearIndependent_log_primes`) makes `(p_i^{−it})` close to `(u_i)`,
  so the vertical translate of `D` is uniformly close to `f` near `0`, and the zeros of `f` move
  with their multiplicity (`HTGeometry.exists_local_zeroSet`).
* **Collide or come close** (`exists_collision_or_close_pair`). Hence for every `δ` there is, at
  arbitrarily large height, either a multiple zero of `D` or two distinct zeros within `2δ`.

With the companion criterion this classifies uniform repulsion for finite-prime carriers whose
tangencies are isolated of finite order: near-coincidences at every scale occur exactly when the
Bohr lift has a consistent tangency.
-/

open Complex Metric Set Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The carrier `s ↦ G(v_i P_i^{−s})`. -/
def translateCarrier {d : ℕ} (P : Fin d → ℝ) (G : (Fin d → ℂ) → ℂ) (v : Fin d → ℂ) (s : ℂ) : ℂ :=
  G fun i => v i * ((P i : ℝ) : ℂ) ^ (-s)

theorem translateCarrier_shift {d : ℕ} (P : Fin d → ℝ) (hP : ∀ i, 0 < P i)
    (G : (Fin d → ℂ) → ℂ) (σ t : ℝ) (w : ℂ) :
    translateCarrier P G 1 ((σ : ℂ) + t * I + w) =
      translateCarrier P G (fun i => ((P i : ℝ) : ℂ) ^ (-((t : ℂ) * I))) ((σ : ℂ) + w) := by
  unfold translateCarrier
  congr 1
  funext i
  have h0 : ((P i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hP i).ne'
  rw [Pi.one_apply, one_mul, ← Complex.cpow_add _ _ h0]
  congr 1
  ring

/-- `P^{−it}` as a Kronecker character. -/
theorem cpow_neg_tI_eq {P : ℝ} (hP : 0 < P) (t : ℝ) :
    ((P : ℝ) : ℂ) ^ (-((t : ℂ) * I)) =
      (starRingEnd ℂ) (GaloisForLFunctions.expChar (Real.log P) t) := by
  unfold GaloisForLFunctions.expChar
  rw [cpow_def_of_ne_zero (by exact_mod_cast hP.ne'), ← Complex.exp_conj,
    ← Complex.ofReal_log hP.le]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Near-coincidences at every scale.** -/
theorem exists_zeros_near_tangency {d : ℕ} (p : Fin d → Nat.Primes) (hp : Function.Injective p)
    {G : (Fin d → ℂ) → ℂ} (hG : Continuous G)
    (hhol : ∀ v : Fin d → ℂ, Differentiable ℂ (translateCarrier (fun i => ((p i : ℕ) : ℝ)) G v))
    {σ : ℝ} {u : Fin d → ℂ} (hu : ∀ i, ‖u i‖ = 1)
    (hzero : translateCarrier (fun i => ((p i : ℕ) : ℝ)) G u σ = 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hiso : ∀ w ∈ closedBall (0 : ℂ) ρ,
      translateCarrier (fun i => ((p i : ℕ) : ℝ)) G u ((σ : ℂ) + w) = 0 → w = 0)
    {δ : ℝ} (hδ : 0 < δ) (T₀ : ℝ) :
    ∃ t : ℝ, T₀ < t ∧ ∃ Z : Finset ℂ, (∀ z ∈ Z, z ∈ ball (0 : ℂ) δ ∧
        translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + z) = 0) ∧
      (∑ z ∈ Z, HTGeometry.zeroMult
          (fun w => translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + w)) z) =
        HTGeometry.zeroMult
          (fun w => translateCarrier (fun i => ((p i : ℕ) : ℝ)) G u ((σ : ℂ) + w)) 0 := by
  classical
  set P : Fin d → ℝ := fun i => ((p i : ℕ) : ℝ) with hPdef
  have hP : ∀ i, 0 < P i := fun i => by
    simp only [hPdef]; exact_mod_cast (p i).2.pos
  set f : ℂ → ℂ := fun w => translateCarrier P G u ((σ : ℂ) + w) with hf
  have hfdiff : Differentiable ℂ f := (hhol u).comp (differentiable_const _ |>.add differentiable_id)
  set δ' : ℝ := min δ (ρ / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  have h2δ' : 2 * δ' ≤ ρ := by have := min_le_right δ (ρ / 2); linarith
  obtain ⟨ε, hε, hloc⟩ := HTGeometry.exists_local_zeroSet isOpen_univ hfdiff.differentiableOn hδ'0
    (subset_univ _) (by simpa [hf] using hzero)
    (fun w hw hw0 => hiso w (closedBall_subset_closedBall h2δ' hw) hw0)
  -- uniform continuity of `(v, w) ↦ G(v_i P_i^{−(σ+w)})` on a compact set
  set Φ : (Fin d → ℂ) × ℂ → ℂ := fun a => translateCarrier P G a.1 ((σ : ℂ) + a.2) with hΦ
  have hΦc : Continuous Φ := by
    refine hG.comp (continuous_pi fun i => ?_)
    refine ((continuous_apply i).comp continuous_fst).mul ?_
    exact Continuous.const_cpow ((continuous_const.add continuous_snd).neg)
      (Or.inl (by exact_mod_cast (hP i).ne'))
  set C : Set ((Fin d → ℂ) × ℂ) := (Set.pi univ fun _ => closedBall (0 : ℂ) 2) ×ˢ
    closedBall (0 : ℂ) (2 * δ') with hC
  have hCc : IsCompact C :=
    (isCompact_univ_pi fun _ => isCompact_closedBall 0 2).prod (isCompact_closedBall 0 _)
  obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hCc.uniformContinuousOn_of_continuous hΦc.continuousOn) ε hε
  -- Kronecker: `P_i^{−it}` close to `u_i`
  have hind : LinearIndependent ℚ fun i => Real.log (P i) :=
    GaloisForLFunctions.linearIndependent_log_primes.comp p hp
  obtain ⟨t, ht, hK⟩ := GaloisForLFunctions.kronecker_approx_atTop hind (fun i => -arg (u i))
    hη T₀
  set v : Fin d → ℂ := fun i => ((P i : ℝ) : ℂ) ^ (-((t : ℂ) * I)) with hv
  have hvu : ∀ i, ‖v i - u i‖ < η := by
    intro i
    have hconj := hK i
    rw [← Complex.norm_conj, map_sub, ← Complex.exp_conj] at hconj
    have hui : (starRingEnd ℂ) ((((-arg (u i)) : ℝ) : ℂ) * I) = ((arg (u i) : ℝ) : ℂ) * I := by
      simp [Complex.conj_ofReal]
    rw [hui] at hconj
    have hexp : Complex.exp (((arg (u i) : ℝ) : ℂ) * I) = u i := by
      have := Complex.norm_mul_exp_arg_mul_I (u i)
      rw [hu i, Complex.ofReal_one, one_mul] at this
      exact this
    rw [hexp, ← cpow_neg_tI_eq (hP i)] at hconj
    exact hconj
  have hvnorm : ∀ i, ‖v i‖ = 1 := fun i => by
    rw [hv, Complex.norm_cpow_eq_rpow_re_of_pos (hP i)]
    simp
  -- the vertical translate is `ε`-close to `f` on `closedBall 0 (2δ')`
  set h : ℂ → ℂ := fun w => translateCarrier P G 1 ((σ : ℂ) + t * I + w) with hh
  have hheq : ∀ w, h w = Φ (v, w) := fun w => translateCarrier_shift P hP G σ t w
  have hclose : ∀ z ∈ closedBall (0 : ℂ) (2 * δ'), ‖h z - f z‖ ≤ ε := by
    intro z hz
    have hmemv : (v, z) ∈ C := ⟨fun i _ => by
      rw [mem_closedBall, dist_zero_right, hvnorm]; norm_num, hz⟩
    have hmemu : (u, z) ∈ C := ⟨fun i _ => by
      rw [mem_closedBall, dist_zero_right, hu]; norm_num, hz⟩
    have hdist : dist (v, z) (u, z) < η := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact (dist_pi_lt_iff hη).mpr fun i => by rw [dist_eq_norm]; exact hvu i
    have := hunif _ hmemv _ hmemu hdist
    rw [dist_eq_norm] at this
    rw [hheq]
    exact this.le
  have hhdiff : Differentiable ℂ h :=
    (hhol 1).comp (differentiable_const _ |>.add differentiable_id)
  obtain ⟨Z, hZball, hZiff, hZsum⟩ := hloc h hhdiff.differentiableOn hclose
  refine ⟨t, ht, Z, fun z hz => ⟨ball_subset_ball (min_le_left _ _) (hZball z hz),
    ((hZiff z (hZball z hz)).mpr hz)⟩, hZsum⟩

/-- **Collide or come close.** Under the hypotheses of `exists_zeros_near_tangency`, if the
tangency has order `≥ 2`, then for every `δ > 0` and `T₀` there is `t > T₀` such that near
`σ + it` the carrier has either a multiple zero or two distinct zeros, all within `δ`. -/
theorem exists_collision_or_close_pair {d : ℕ} (p : Fin d → Nat.Primes)
    (hp : Function.Injective p) {G : (Fin d → ℂ) → ℂ} (hG : Continuous G)
    (hhol : ∀ v : Fin d → ℂ, Differentiable ℂ (translateCarrier (fun i => ((p i : ℕ) : ℝ)) G v))
    {σ : ℝ} {u : Fin d → ℂ} (hu : ∀ i, ‖u i‖ = 1)
    (hzero : translateCarrier (fun i => ((p i : ℕ) : ℝ)) G u σ = 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hiso : ∀ w ∈ closedBall (0 : ℂ) ρ,
      translateCarrier (fun i => ((p i : ℕ) : ℝ)) G u ((σ : ℂ) + w) = 0 → w = 0)
    (hord : 2 ≤ HTGeometry.zeroMult
      (fun w => translateCarrier (fun i => ((p i : ℕ) : ℝ)) G u ((σ : ℂ) + w)) 0)
    {δ : ℝ} (hδ : 0 < δ) (T₀ : ℝ) :
    ∃ t : ℝ, T₀ < t ∧
      ((∃ z ∈ ball (0 : ℂ) δ,
          translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + z) = 0 ∧
          2 ≤ HTGeometry.zeroMult
            (fun w => translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + w)) z) ∨
        ∃ z ∈ ball (0 : ℂ) δ, ∃ z' ∈ ball (0 : ℂ) δ, z ≠ z' ∧
          translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + z) = 0 ∧
          translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + z') = 0) := by
  classical
  obtain ⟨t, ht, Z, hZ, hsum⟩ := exists_zeros_near_tangency p hp hG hhol hu hzero hρ hiso hδ T₀
  refine ⟨t, ht, ?_⟩
  set m := fun z => HTGeometry.zeroMult
    (fun w => translateCarrier (fun i => ((p i : ℕ) : ℝ)) G 1 ((σ : ℂ) + t * I + w)) z
  by_cases hmult : ∃ z ∈ Z, 2 ≤ m z
  · obtain ⟨z, hz, hm⟩ := hmult
    exact Or.inl ⟨z, (hZ z hz).1, (hZ z hz).2, hm⟩
  · push Not at hmult
    refine Or.inr ?_
    have hcard : 2 ≤ Z.card := by
      have hle : (∑ z ∈ Z, m z) ≤ ∑ _z ∈ Z, 1 := Finset.sum_le_sum fun z hz => by
        have := hmult z hz; omega
      rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
      have : 2 ≤ ∑ z ∈ Z, m z := hsum ▸ hord
      omega
    obtain ⟨z, hz, z', hz', hne⟩ := Finset.one_lt_card.mp hcard
    exact ⟨z, (hZ z hz).1, z', (hZ z' hz').1, hne, (hZ z hz).2, (hZ z' hz').2⟩

end GaloisForLFunctions.ArithmeticDiscreteness
