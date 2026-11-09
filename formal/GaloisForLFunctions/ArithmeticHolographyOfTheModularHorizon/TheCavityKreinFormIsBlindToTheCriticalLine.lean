import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheOddCavitySeesEveryResonance
import GaloisForLFunctions.HTGeometry.HermitianInertia
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# The Krein form of the cavity is blind to the critical line

At a resonance `s = ρ/2` the energy pairing `b_s(g, h) = ∫_𝒟 g h̄ E*(s − ½)` of the mirror-even channel is a
bounded sesquilinear form on cavity functions. Its Hermitian part

  `𝒦_s(g, h) = ½(b_s(g, h) + conj b_s(h, g))`

is the **resonance Krein form** of the horizon (`resonanceKrein`). This module determines its inertia on the
odd cavity.

**The tents diagonalize it.** Tent fields with different indices have disjoint supports, so
`b_s(G_j, G_k) = 0` for `j ≠ k` and the Gram matrix of finitely many tents is
`diag(Re d_j(s))` (`kreinGram_eq_diagonal`), `d_j(s) = ∫_𝒟 G_j² E*(s − ½)` the tent energy.

**The Krein signature rotates.** By the phase law of the tent energies, far up the cusp `Re d_j(s) > 0` when
`cos(arg κ − Im s · log(j + 7/2)) ≥ ¾` and `Re d_j(s) < 0` when it is `≤ −¾` (`tent_krein_sign`). A zero of
`ζ` with `Re ρ > 0` is never real (`im_ne_zero_of_zero`), so the phases `Im s · log(j + 7/2)` move with steps
tending to `0` and meet every arc infinitely often (`exists_cos_ge`).

**Infinite index of both signs at every resonance** (`krein_index_tents`). For every zero `ρ` of `ζ` with
`Re ρ > 0` and every `n` there are `n` tents on which `𝒦_{ρ/2}` is negative definite and `n` on which it is
positive definite. This holds at critical zeros `ρ = ½ + iγ` as well as off the line: the horizon's own Krein
form does not distinguish damping `¼` from any other rate. The Krein index that counts zeros right of the line
is the Weil form of the zero side (`ArithmeticOrientationGeometry.orientationIndex_law`); the horizon carries
the frequency `Im s` of a resonance as the rotation speed of the Krein signs, not in an index.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open BlackHoleRingdown.OddCusp (reduceSL)

/-! ### The resonance Krein form -/

/-- The resonance Krein form `𝒦_s(g, h) = ½(b_s(g, h) + conj b_s(h, g))`. -/
def resonanceKrein (s : ℂ) (g h : ℍ → ℂ) : ℂ := (pairing s g h + starRingEnd ℂ (pairing s h g)) / 2

theorem resonanceKrein_symm (s : ℂ) (g h : ℍ → ℂ) :
    resonanceKrein s h g = starRingEnd ℂ (resonanceKrein s g h) := by
  unfold resonanceKrein
  rw [map_div₀, map_add, Complex.conj_conj, map_ofNat, add_comm]

/-! ### The tents are orthogonal -/

theorem tent_mul_eq_zero {j k : ℕ} (hjk : j ≠ k) (y : ℝ) : tent j y * tent k y = 0 := by
  by_contra h
  have mem : ∀ {i : ℕ}, tent i y ≠ 0 → y ∈ Ioo ((i : ℝ) + 3) (i + 4) := fun {i} hi => by
    by_contra hn
    simp only [mem_Ioo, not_and_or, not_lt] at hn
    refine hi (tent_eq_zero ?_)
    rcases hn with hn | hn
    · left; linarith
    · right; linarith
  have hj := mem (left_ne_zero_of_mul h)
  have hk := mem (right_ne_zero_of_mul h)
  have h1 : (j : ℝ) < k + 1 := by linarith [hj.1, hk.2]
  have h2 : (k : ℝ) < j + 1 := by linarith [hk.1, hj.2]
  have h1' : j < k + 1 := by exact_mod_cast h1
  have h2' : k < j + 1 := by exact_mod_cast h2
  omega

/-- Tent fields with different indices have disjoint supports. -/
theorem oddCuspField_tent_mul_eq_zero {j k : ℕ} (hjk : j ≠ k) (z : ℍ) :
    oddCuspField (tent j) z * oddCuspField (tent k) z = 0 := by
  unfold oddCuspField oddProfile
  rw [mul_mul_mul_comm, tent_mul_eq_zero hjk, zero_mul]

theorem pairing_tent_eq_zero {j k : ℕ} (hjk : j ≠ k) (s : ℂ) :
    pairing s (fun z => (oddCuspField (tent j) z : ℂ)) (fun z => (oddCuspField (tent k) z : ℂ)) = 0 := by
  unfold pairing
  refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans (integral_zero _ _)
  simp only [pairIntegrand, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, oddCuspField_tent_mul_eq_zero hjk, Complex.ofReal_zero, zero_mul]

/-- The Krein Gram matrix of the tent fields `G_j`, `j ∈ S`, at `s`. -/
def kreinGram (s : ℂ) (S : Finset ℕ) : Matrix S S ℂ := fun j k =>
  resonanceKrein s (fun z => (oddCuspField (tent j) z : ℂ)) (fun z => (oddCuspField (tent k) z : ℂ))

/-- **The tents diagonalize the Krein form**: `𝒦_s(G_j, G_k) = δ_{jk} Re d_j(s)`. -/
theorem kreinGram_eq_diagonal (s : ℂ) (S : Finset ℕ) :
    kreinGram s S = Matrix.diagonal fun j : S => (((tentEnergy s j).re : ℝ) : ℂ) := by
  ext j k
  by_cases h : j = k
  · subst h
    rw [Matrix.diagonal_apply_eq]
    show (tentEnergy s j + starRingEnd ℂ (tentEnergy s j)) / 2 = _
    rw [Complex.add_conj]
    push_cast
    ring
  · have hjk : (j : ℕ) ≠ k := fun e => h (Subtype.ext e)
    rw [Matrix.diagonal_apply_ne _ h]
    simp only [kreinGram, resonanceKrein, pairing_tent_eq_zero hjk, pairing_tent_eq_zero hjk.symm, map_zero,
      add_zero, zero_div]

theorem posIndex_kreinGram (s : ℂ) (S : Finset ℕ) :
    hermPosIndex (kreinGram s S) = ({j | 0 < (tentEnergy s j).re} : Finset S).card := by
  rw [kreinGram_eq_diagonal, posIndex_diagonal]

theorem negIndex_kreinGram (s : ℂ) (S : Finset ℕ) :
    hermNegIndex (kreinGram s S) = ({j | (tentEnergy s j).re < 0} : Finset S).card := by
  rw [hermNegIndex, kreinGram_eq_diagonal, Matrix.diagonal_neg]
  have : (fun j : S => -(((tentEnergy s j).re : ℝ) : ℂ)) = fun j : S => ((-(tentEnergy s j).re : ℝ) : ℂ) := by
    funext j; push_cast; ring
  rw [this, posIndex_diagonal]
  congr 1
  ext j
  simp

/-! ### The phases meet every arc -/

/-- Consecutive phases `τ log(m + 7/2)` differ by at most `τ/(m + 7/2)`. -/
theorem phase_step_le {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    τ * Real.log ((m + 1 : ℕ) + 7 / 2) - τ * Real.log (m + 7 / 2) ≤ τ / (m + 7 / 2) := by
  have h0 : (0 : ℝ) < m + 7 / 2 := by positivity
  have h1 : (0 : ℝ) < (m + 1 : ℕ) + 7 / 2 := by positivity
  have hlog : Real.log ((m + 1 : ℕ) + 7 / 2) - Real.log (m + 7 / 2) ≤ 1 / (m + 7 / 2) := by
    rw [← Real.log_div h1.ne' h0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos h1 h0)).trans_eq ?_
    push_cast
    field_simp
    ring
  calc τ * Real.log ((m + 1 : ℕ) + 7 / 2) - τ * Real.log (m + 7 / 2)
      = τ * (Real.log ((m + 1 : ℕ) + 7 / 2) - Real.log (m + 7 / 2)) := by ring
    _ ≤ τ * (1 / (m + 7 / 2)) := mul_le_mul_of_nonneg_left hlog hτ.le
    _ = τ / (m + 7 / 2) := by ring

theorem exists_cos_ge_of_pos {τ : ℝ} (hτ : 0 < τ) (ψ : ℝ) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ 3 / 4 ≤ Real.cos (ψ - τ * Real.log (j + 7 / 2)) := by
  set v : ℕ → ℝ := fun j => τ * Real.log (j + 7 / 2)
  have hv_mono : Monotone v := fun i j hij => by
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have : (i : ℝ) + 7 / 2 ≤ j + 7 / 2 := by linarith
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) this) hτ.le
  set M : ℕ := max N ⌈2 * τ⌉₊
  set k : ℤ := ⌈(v M - ψ) / (2 * Real.pi)⌉
  set T : ℝ := ψ + k * (2 * Real.pi)
  have hTM : v M ≤ T := by
    have h := Int.le_ceil ((v M - ψ) / (2 * Real.pi))
    rw [div_le_iff₀ (by positivity)] at h
    simp only [T, k]
    linarith
  have hex : ∃ j, M ≤ j ∧ T ≤ v j := by
    refine ⟨max M ⌈Real.exp (T / τ)⌉₊, le_max_left _ _, ?_⟩
    refine le_trans ?_ (hv_mono (le_max_right M _))
    have hc : Real.exp (T / τ) ≤ (⌈Real.exp (T / τ)⌉₊ : ℝ) + 7 / 2 := by
      linarith [Nat.le_ceil (Real.exp (T / τ))]
    have hlog := (Real.le_log_iff_exp_le (by positivity)).2 hc
    show T ≤ τ * Real.log ((⌈Real.exp (T / τ)⌉₊ : ℝ) + 7 / 2)
    rw [div_le_iff₀ hτ] at hlog
    linarith
  classical
  set j := Nat.find hex
  have hj : M ≤ j ∧ T ≤ v j := Nat.find_spec hex
  have hjT : v j ≤ T + 1 / 2 := by
    by_cases hjM : j = M
    · rw [hjM]; linarith
    · obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hmM : M ≤ m := by omega
      have hnot : ¬(M ≤ m ∧ T ≤ v m) := Nat.find_min hex (by omega)
      have hvm : v m < T := by
        by_contra h; exact hnot ⟨hmM, not_lt.1 h⟩
      have hstep := phase_step_le hτ m
      have h2τ : 2 * τ ≤ (m : ℝ) + 7 / 2 := by
        have : (⌈2 * τ⌉₊ : ℝ) ≤ m := by exact_mod_cast (le_max_right N _).trans hmM
        linarith [Nat.le_ceil (2 * τ)]
      have hq : τ / ((m : ℝ) + 7 / 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have : v j = τ * Real.log ((m + 1 : ℕ) + 7 / 2) := by rw [hm]
      linarith
  refine ⟨j, (le_max_left N _).trans hj.1, ?_⟩
  have hper : Real.cos (ψ - τ * Real.log (j + 7 / 2)) = Real.cos (T - v j) := by
    rw [show ψ - τ * Real.log (j + 7 / 2) = (T - v j) - k * (2 * Real.pi) by simp only [T, v]; ring,
      Real.cos_sub_int_mul_two_pi]
  rw [hper]
  have hd : (T - v j) ^ 2 ≤ 1 / 4 := by nlinarith [hj.2]
  linarith [Real.one_sub_sq_div_two_le_cos (x := T - v j)]

/-- **The phases meet every arc beyond every index**: for `τ ≠ 0`, every `ψ` and `N` there is `j ≥ N` with
`cos(ψ − τ log(j + 7/2)) ≥ ¾`. -/
theorem exists_cos_ge {τ : ℝ} (hτ : τ ≠ 0) (ψ : ℝ) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ 3 / 4 ≤ Real.cos (ψ - τ * Real.log (j + 7 / 2)) := by
  rcases lt_or_gt_of_ne hτ with h | h
  · obtain ⟨j, hj, hc⟩ := exists_cos_ge_of_pos (neg_pos.2 h) (-ψ) N
    refine ⟨j, hj, ?_⟩
    rw [show ψ - τ * Real.log (j + 7 / 2) = -(-ψ - -τ * Real.log (j + 7 / 2)) by ring, Real.cos_neg]
    exact hc
  · exact exists_cos_ge_of_pos h ψ N

/-! ### Infinite index of both signs -/

/-- A zero of `ζ` with positive real part is not real. -/
theorem im_ne_zero_of_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) : ρ.im ≠ 0 := by
  intro him
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  exact riemannZeta_real_strip_ne_zero hpos hlt (hρ ▸ hζ)

/-- **The Krein sign law of the tents.** Far up the cusp the sign of `Re d_j(ρ/2)` is the sign of
`cos(arg κ − Im(ρ/2) log(j + 7/2))` whenever the latter has modulus at least `¾`. -/
theorem tent_krein_sign {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      (3 / 4 ≤ Real.cos ((resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2)) →
        0 < (tentEnergy (ρ / 2) j).re) ∧
      (Real.cos ((resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2)) ≤ -(3 / 4) →
        (tentEnergy (ρ / 2) j).re < 0) := by
  obtain ⟨J, hJ⟩ := exists_tent_phase_pos hζ hpos
  refine ⟨J, fun j hj => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · have := hJ j hj 0 (by rw [zero_add]; exact hc)
    simpa using this
  · have := hJ j hj Real.pi (by
      rw [show Real.pi + (resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2) =
        ((resonanceCoefficient (ρ / 2 - 1 / 2)).arg - (ρ / 2).im * Real.log (j + 7 / 2)) + Real.pi by ring,
        Real.cos_add_pi]
      linarith)
    rw [Complex.exp_pi_mul_I] at this
    simpa using this

/-- **The cavity Krein form has infinite index of both signs at every resonance.** For every zero `ρ` of `ζ`
with `Re ρ > 0`, on the critical line or off it, and every `n`, there are `n` tent fields on which the resonance
Krein form `𝒦_{ρ/2}` is negative definite and `n` on which it is positive definite. -/
theorem krein_index_tents {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) (n : ℕ) :
    (∃ S : Finset ℕ, S.card = n ∧ hermNegIndex (kreinGram (ρ / 2) S) = n) ∧
      ∃ S : Finset ℕ, S.card = n ∧ hermPosIndex (kreinGram (ρ / 2) S) = n := by
  obtain ⟨J, hJ⟩ := tent_krein_sign hζ hpos
  have hτ : (ρ / 2).im ≠ 0 := by
    have := im_ne_zero_of_zero hζ hpos
    simpa using this
  set ψ := (resonanceCoefficient (ρ / 2 - 1 / 2)).arg
  have hneg : {j : ℕ | (tentEnergy (ρ / 2) j).re < 0}.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun M => ?_
    obtain ⟨j, hj, hc⟩ := exists_cos_ge hτ (ψ + Real.pi) (max J (M + 1))
    refine ⟨j, (hJ j ((le_max_left _ _).trans hj)).2 ?_, by omega⟩
    rw [show ψ - (ρ / 2).im * Real.log (j + 7 / 2) = (ψ + Real.pi - (ρ / 2).im * Real.log (j + 7 / 2)) -
      Real.pi by ring, Real.cos_sub_pi]
    linarith
  have hposs : {j : ℕ | 0 < (tentEnergy (ρ / 2) j).re}.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun M => ?_
    obtain ⟨j, hj, hc⟩ := exists_cos_ge hτ ψ (max J (M + 1))
    exact ⟨j, (hJ j ((le_max_left _ _).trans hj)).1 hc, by omega⟩
  constructor
  · obtain ⟨S, hS, hcard⟩ := hneg.exists_subset_card_eq n
    refine ⟨S, hcard, ?_⟩
    rw [negIndex_kreinGram, ← hcard, ← Finset.card_attach (s := S)]
    congr 1
    ext j
    simpa using hS j.2
  · obtain ⟨S, hS, hcard⟩ := hposs.exists_subset_card_eq n
    refine ⟨S, hcard, ?_⟩
    rw [posIndex_kreinGram, ← hcard, ← Finset.card_attach (s := S)]
    congr 1
    ext j
    simpa using hS j.2

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
