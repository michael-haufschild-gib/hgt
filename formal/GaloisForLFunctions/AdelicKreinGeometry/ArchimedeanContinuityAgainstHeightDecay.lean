import GaloisForLFunctions.AdelicKreinGeometry.ConformalSymmetryNeedsANegativeSquare
import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# Archimedean continuity against height decay

The additive and multiplicative structures of `ℚ` meet on the dilations through two incompatible
regularities: an archimedean state is continuous at `1` in the real topology, a finite-adelic state
decays with the denominator. Rationals near `1` have huge denominators, so the two cannot be
subtracted at finite index.

* **Near coincidence** (`negIndex_sub_eq_top`). Let `F` be continuous at `1`, `ψ` tend to `0` with the
  denominator and `ψ(1) > 0`. The points `u_i = (K + i)/K` have ratios `≠ 1` within `L/K` of `1`,
  hence denominators at least `K/L` (`one_le_den_mul_abs_sub_one`). On the polar hyperplane the Gram
  matrix of `F − ψ` is within `2εL` of `−ψ(1)·I`: `L` negative squares for every `L`.
* **Dilution** (`negIndex_le_negIndex_slope_add`). For a Hecke-supported `ψ` and a slope state
  `s(|a|)`, spread a coefficient vector over the translates `x ↦ x + j/P`, `j < P`, of the dilations.
  The slope part is unchanged, the off-diagonal Hecke terms vanish (the shift `(j' − j)/(P u)` has `P`
  in its denominator, `den_ne_one_of_prime_mul`), and the diagonal ones are divided by `P`. Lower
  semicontinuity gives `κ(s) ≤ κ(s(|a|) + ψ)`.
* **No continuous dilation part** (`negIndex_slope_add_eq_top`). If `ψ` is positive, Hecke-supported
  and has the integer successor, then `ψ` decays on the dilations (`(nd)|ψ|² ≤ 1`). Whenever the
  dilation part `s + ψ` of `s(|a|) + ψ` is continuous at `1`, the state has infinite index; in
  particular when it is Weil's correlation (`negIndex_eq_top_of_weil_slope_add`).

This class contains every Hecke-supported state (`s = 0`) and every Haar state corrected by an
archimedean slope function, such as `haarOneNegativeSquare`, whose dilation reading must therefore
be discontinuous at `1`. A Pontryagin carrier of Weil's correlation with the integer successor must
couple the slope and the shift in a way no slope correction of a positive state does.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Near coincidence -/

/-- A rational `q ≠ 1` has denominator at least `1/|q − 1|`. -/
theorem one_le_den_mul_abs_sub_one {q : ℚ} (hq : q ≠ 1) : 1 ≤ (q.den : ℚ) * |q - 1| := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have e : (q.den : ℚ) * (q - 1) = ((q.num - q.den : ℤ) : ℚ) := by
    have := Rat.mul_den_eq_num q
    push_cast
    linarith
  have hne : q.num - q.den ≠ 0 := by
    intro h
    apply hq
    have h0 : (q.den : ℚ) * (q - 1) = 0 := by rw [e, h]; simp
    have := (mul_eq_zero.mp h0).resolve_left hd.ne'
    linarith
  rw [← abs_of_pos hd, ← abs_mul, e]
  exact_mod_cast Int.one_le_abs hne

/-- A double sum against coefficients is bounded by the largest entry times `(Σ‖c‖)²`. -/
theorem norm_doubleSum_le {n : ℕ} (c : Fin n → ℂ) (E : Fin n → Fin n → ℂ) {B : ℝ}
    (hE : ∀ i j, ‖E i j‖ ≤ B) :
    ‖∑ i, ∑ j, conj (c i) * E i j * c j‖ ≤ B * (∑ i, ‖c i‖) ^ 2 := by
  calc ‖∑ i, ∑ j, conj (c i) * E i j * c j‖ ≤ ∑ i, ∑ j, ‖c i‖ * B * ‖c j‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (sum_le_sum fun j _ => ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
        exact hE i j
    _ = B * (∑ i, ‖c i‖) ^ 2 := by
        rw [sq, sum_mul_sum, mul_sum]
        exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

/-- **Near coincidence.** A state continuous at `1` minus a state decaying with the denominator,
positive at `1`, has infinitely many negative squares. -/
theorem negIndex_sub_eq_top {F ψ : posUnits → ℂ}
    (hF : ∀ ε > 0, ∃ δ > 0, ∀ u : posUnits, |((u : ℚˣ) : ℚ) - 1| < δ → ‖F u - F 1‖ < ε)
    (hψ : ∀ ε > 0, ∃ N : ℕ, ∀ u : posUnits, N ≤ ((u : ℚˣ) : ℚ).den → ‖ψ u‖ < ε)
    {a : ℝ} (ha : 0 < a) (hψ1 : ψ 1 = a) : negIndex (fun u => F u - ψ u) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun L => ?_
  set n := L + 1
  set ε : ℝ := a / (4 * n)
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hFδ⟩ := hF ε hε
  obtain ⟨N, hN⟩ := hψ ε hε
  -- a scale `K` making all ratios close to `1` with large denominators
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, (n : ℚ) * (N + 1) ≤ K ∧ (n : ℚ) / K < δ := by
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt ((n : ℚ) / δ)
    refine ⟨max K₀ (n * (N + 1)), by push_cast; exact_mod_cast le_max_right _ _, ?_⟩
    have hKpos : (0 : ℚ) < max K₀ (n * (N + 1)) := by
      have : (0 : ℚ) < n * (N + 1) := by positivity
      exact lt_of_lt_of_le this (by exact_mod_cast le_max_right _ _)
    rw [div_lt_iff₀ hKpos]
    calc (n : ℚ) = n / δ * δ := by field_simp
      _ < K₀ * δ := by gcongr
      _ ≤ (max K₀ (n * (N + 1)) : ℕ) * δ := by gcongr; exact_mod_cast le_max_left _ _
      _ = δ * (max K₀ (n * (N + 1)) : ℕ) := mul_comm _ _
  have hKpos : (0 : ℚ) < K := lt_of_lt_of_le (by positivity) hK1
  set x : Fin n → posUnits := fun i => ⟨Units.mk0 (((K : ℚ) + i) / K) (by positivity),
    by show (0 : ℚ) < ((Units.mk0 _ _ : ℚˣ) : ℚ); rw [Units.val_mk0]; positivity⟩
  have hratio : ∀ i j : Fin n, (((x i)⁻¹ * x j : posUnits) : ℚˣ) = (((K : ℚ) + j) / (K + i)) := by
    intro i j
    simp only [x, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    field_simp
  have hclose : ∀ i j : Fin n, |(((x i)⁻¹ * x j : posUnits) : ℚˣ) - (1 : ℚ)| < δ := by
    intro i j
    rw [hratio]
    have hKi : (0 : ℚ) < K + i := by positivity
    rw [show ((K : ℚ) + j) / (K + i) - 1 = ((j : ℚ) - i) / (K + i) by field_simp; ring,
      abs_div, abs_of_pos hKi]
    have hij : |(j : ℚ) - i| ≤ n := by
      have hj : (j : ℚ) < n := by exact_mod_cast j.2
      have hi : (i : ℚ) < n := by exact_mod_cast i.2
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg (α := ℚ) (j : ℕ)),
        (Nat.cast_nonneg (α := ℚ) (i : ℕ))]
    calc |(j : ℚ) - i| / (K + i) ≤ n / K := by
          apply div_le_div₀ (by positivity) hij hKpos (by linarith [(Nat.cast_nonneg (α := ℚ) (i : ℕ))])
      _ < δ := hK2
  have hden : ∀ i j : Fin n, i ≠ j → N ≤ ((((x i)⁻¹ * x j : posUnits) : ℚˣ) : ℚ).den := by
    intro i j hij
    set q := ((((x i)⁻¹ * x j : posUnits) : ℚˣ) : ℚ)
    have hq1 : q ≠ 1 := by
      intro h
      apply hij
      have h' := hratio i j
      rw [show (((x i)⁻¹ * x j : posUnits) : ℚˣ) = q from rfl, h] at h'
      have hKi : (K : ℚ) + i ≠ 0 := by positivity
      have := (eq_div_iff hKi).mp h'
      exact Fin.ext (by exact_mod_cast (by linarith : (i : ℚ) = j))
    have h1 := one_le_den_mul_abs_sub_one hq1
    have h2 : |q - 1| < (n : ℚ) / K := by
      have hq' : q = ((K : ℚ) + j) / (K + i) := hratio i j
      rw [hq']
      have hKi : (0 : ℚ) < K + i := by positivity
      rw [show ((K : ℚ) + j) / (K + i) - 1 = ((j : ℚ) - i) / (K + i) by field_simp; ring,
        abs_div, abs_of_pos hKi]
      have hji : |(j : ℚ) - i| < n := by
        have hj : (j : ℚ) < n := by exact_mod_cast j.2
        have hi : (i : ℚ) < n := by exact_mod_cast i.2
        rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg (α := ℚ) (j : ℕ)),
          (Nat.cast_nonneg (α := ℚ) (i : ℕ))]
      calc |(j : ℚ) - i| / (K + i) ≤ |(j : ℚ) - i| / K :=
            div_le_div_of_nonneg_left (abs_nonneg _) hKpos (by linarith [(Nat.cast_nonneg (α := ℚ)
              (i : ℕ))])
        _ < n / K := by gcongr
    have hdpos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have h3 : (1 : ℚ) < q.den * (n / K) := lt_of_le_of_lt h1 (by gcongr)
    have h4 : (N : ℚ) < q.den := by
      have h5 : (K : ℚ) < q.den * n := by
        have := h3; rw [mul_div_assoc', lt_div_iff₀ hKpos, one_mul] at this; exact this
      have h6 : (n : ℚ) * N < n * q.den := by nlinarith
      exact lt_of_mul_lt_mul_left h6 (by positivity)
    exact_mod_cast h4.le
  -- the polar hyperplane is negative definite
  have hneg : IsPosDefOn (-gram (fun u => F u - ψ u) x) (LinearMap.ker (totalMass (Fin n))) := by
    intro c hc hc0
    have hsum : ∑ i, c i = 0 := hc
    rw [hermQuad_neg, neg_pos, hermQuad_gram]
    set E : Fin n → Fin n → ℂ := fun i j => (F ((x i)⁻¹ * x j) - F 1) -
      (ψ ((x i)⁻¹ * x j) - if i = j then (a : ℂ) else 0)
    have hE : ∀ i j, ‖E i j‖ ≤ 2 * ε := by
      intro i j
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖F ((x i)⁻¹ * x j) - F 1‖ ≤ ε := (hFδ _ (hclose i j)).le
      have h2 : ‖ψ ((x i)⁻¹ * x j) - if i = j then (a : ℂ) else 0‖ ≤ ε := by
        split_ifs with h
        · subst h; rw [inv_mul_cancel, hψ1, sub_self, norm_zero]; exact hε.le
        · rw [sub_zero]; exact (hN _ (hden i j h)).le
      linarith
    have hsplit : ∀ i j, F ((x i)⁻¹ * x j) - ψ ((x i)⁻¹ * x j) =
        F 1 - (if i = j then (a : ℂ) else 0) + E i j := fun i j => by simp only [E]; ring
    have e : ∀ i j, conj (c i) * (F ((x i)⁻¹ * x j) - ψ ((x i)⁻¹ * x j)) * c j =
        F 1 * (conj (c i) * c j) + (-(a : ℂ) * (if i = j then conj (c i) * c j else 0) +
          conj (c i) * E i j * c j) := fun i j => by
      rw [hsplit]; split_ifs <;> ring
    have h1 : ∑ i, ∑ j, F 1 * (conj (c i) * c j) = 0 := by
      have : ∑ i, ∑ j, F 1 * (conj (c i) * c j) = F 1 * ((∑ i, conj (c i)) * ∑ j, c j) := by
        rw [sum_mul_sum, mul_sum]; simp_rw [mul_sum]
      rw [this, hsum, mul_zero, mul_zero]
    have h2 : ∑ i, ∑ j, -(a : ℂ) * (if i = j then conj (c i) * c j else 0) =
        -(a : ℂ) * ∑ i, conj (c i) * c i := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [← mul_sum, Finset.sum_ite_eq, if_pos (mem_univ _)]
    have hS : ∑ i, ∑ j, conj (c i) * (F ((x i)⁻¹ * x j) - ψ ((x i)⁻¹ * x j)) * c j =
        -(a : ℂ) * ∑ i, conj (c i) * c i + ∑ i, ∑ j, conj (c i) * E i j * c j := by
      simp_rw [e, sum_add_distrib]
      rw [h1, h2, zero_add]
    have hnormS : ∑ i, conj (c i) * c i = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact sum_congr rfl fun i _ => by rw [Complex.conj_mul']
    have hSpos : 0 < ∑ i, ‖c i‖ ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h; push Not at h; exact hc0 (funext h)
      exact lt_of_lt_of_le (by positivity : 0 < ‖c i‖ ^ 2)
        (Finset.single_le_sum (f := fun i => ‖c i‖ ^ 2) (fun _ _ => by positivity) (mem_univ i))
    have hR : (∑ i, ∑ j, conj (c i) * E i j * c j).re ≤ (a / 2) * ∑ i, ‖c i‖ ^ 2 := by
      refine (Complex.re_le_norm _).trans ((norm_doubleSum_le c E hE).trans ?_)
      have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i => ‖c i‖)
      rw [card_univ, Fintype.card_fin] at hcs
      have hn : (0 : ℝ) < n := by positivity
      calc 2 * ε * (∑ i, ‖c i‖) ^ 2 ≤ 2 * ε * (n * ∑ i, ‖c i‖ ^ 2) := by gcongr
        _ = (a / 2) * ∑ i, ‖c i‖ ^ 2 := by simp only [ε]; field_simp; ring
    rw [hS, hnormS, Complex.add_re]
    have : (-(a : ℂ) * ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ)).re = -a * ∑ i, ‖c i‖ ^ 2 := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [this]
    nlinarith
  have h := finrank_le_posIndex hneg
  have hfr : Module.finrank ℂ (LinearMap.ker (totalMass (Fin n))) = L := finrank_ker_totalMass L
  have h' : Module.finrank ℂ (LinearMap.ker (totalMass (Fin n))) ≤
      hermNegIndex (gram (fun u => F u - ψ u) x) := h
  have hL : L ≤ hermNegIndex (gram (fun u => F u - ψ u) x) := hfr.symm.trans_le h'
  exact (Nat.cast_le.mpr hL).trans (hermNegIndex_gram_le_negIndex _ x)

/-! ### Dilution -/

/-- A prime above `d`, `den α` and `|e|` keeps `d·(e/P)/α` from being an integer. -/
theorem den_ne_one_of_prime_mul {P : ℕ} (hP : P.Prime) {d : ℕ} {α : ℚ} {e : ℤ} (hα : α ≠ 0)
    (hd : ¬ P ∣ d) (hF : ¬ P ∣ α.den) (he : ¬ (P : ℤ) ∣ e) :
    ((d : ℚ) * ((e : ℚ) / P / α)).den ≠ 1 := by
  intro h1
  obtain ⟨N, hN⟩ := (den_eq_one_iff_exists _).mp h1
  set A := α.num
  set F := α.den
  have hαe : α = (A : ℚ) / F := (Rat.num_div_den α).symm
  have hPpos : (P : ℚ) ≠ 0 := by exact_mod_cast hP.pos.ne'
  have hFpos : (F : ℚ) ≠ 0 := by exact_mod_cast α.den_pos.ne'
  have hAne : (A : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hα
  rw [hαe] at hN
  have h : (((d : ℤ) * e * F : ℤ) : ℚ) = ((N * A * P : ℤ) : ℚ) := by
    push_cast
    rw [hN]
    field_simp
  have h' : ((d : ℤ) * e * F : ℤ) = N * A * P := by exact_mod_cast h
  have hdiv : (P : ℤ) ∣ (d : ℤ) * e * F := ⟨N * A, by rw [h']; ring⟩
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
  rcases hPz.dvd_or_dvd hdiv with h | h
  · rcases hPz.dvd_or_dvd h with h | h
    · exact hd (Int.natCast_dvd_natCast.mp h)
    · exact he h
  · exact hF (Int.natCast_dvd_natCast.mp h)

/-- The spread family: the translates `x ↦ x + j/P` of the dilations `x ↦ u_k x`. -/
def spreadFamily {M : ℕ} (P : ℕ) (u : Fin M → posUnits) (p : Fin P × Fin M) : AffineGroupQ :=
  translation ((p.1 : ℚ) / P) * dilation (u p.2 : ℚˣ)

theorem spreadFamily_inv_mul {M P : ℕ} (u : Fin M → posUnits) (j j' : Fin P) (k l : Fin M) :
    (spreadFamily P u (j, k))⁻¹ * spreadFamily P u (j', l) =
      (dilation (u k : ℚˣ))⁻¹ * (translation (((j' : ℚ) - j) / P) * dilation (u l : ℚˣ)) := by
  simp only [spreadFamily, mul_inv_rev, mul_assoc]
  rw [← mul_assoc (translation _)⁻¹, translation_inv_mul]
  congr 3
  ring

/-- **Dilution.** Adding a Hecke-supported function never lowers the index of a slope state. -/
theorem negIndex_le_negIndex_slope_add {s : posUnits → ℂ} (hs : IsHermKernel s)
    {ψ : AffineGroupQ → ℂ} (hψ : IsHeckeSupported ψ) :
    negIndex s ≤ negIndex (fun g => s (slopeAbs g) + ψ g) := by
  classical
  refine negIndex_le_iff.mpr fun M u => ?_
  set φ : AffineGroupQ → ℂ := fun g => s (slopeAbs g) + ψ g
  set ψD : posUnits → ℂ := fun v => ψ (dilation (v : ℚˣ))
  set bound : ℕ := ∑ k, ∑ l, ((((u k : ℚˣ) : ℚ)⁻¹ * ((u l : ℚˣ) : ℚ)).den + ((u k : ℚˣ) : ℚ).den)
  have hprime : ∀ n : ℕ, ∃ P, n + bound + 1 ≤ P ∧ P.Prime := fun n => Nat.exists_infinite_primes _
  choose P hPge hP using hprime
  -- the compressed Gram matrices
  set A : ℕ → Matrix (Fin M) (Fin M) ℂ :=
    fun n => gram s u + (((1 : ℝ) / P n : ℝ) : ℂ) • gram ψD u
  have hentry : ∀ n (j j' : Fin (P n)) (k l : Fin M),
      φ ((spreadFamily (P n) u (j, k))⁻¹ * spreadFamily (P n) u (j', l)) =
        s ((u k)⁻¹ * u l) + if j = j' then ψD ((u k)⁻¹ * u l) else 0 := by
    intro n j j' k l
    rw [spreadFamily_inv_mul]
    simp only [φ, map_mul, map_inv, slopeAbs_translation, one_mul, slopeAbs_dilation]
    congr 1
    split_ifs with hjj
    · subst hjj
      rw [sub_self, zero_div, translation_zero, one_mul, ← map_inv, ← map_mul]
      rfl
    · by_contra hne
      have h1 := hψ _ hne
      rw [affSlope_inv_mul_translation_mul, affShift_inv_mul_translation_mul, affShift_dilation,
        affShift_dilation, sub_self, zero_add, affSlope_dilation, affSlope_dilation] at h1
      have hfab : (((u k : ℚˣ) : ℚ)⁻¹ * ((u l : ℚˣ) : ℚ)).den + ((u k : ℚˣ) : ℚ).den ≤ bound :=
        (Finset.single_le_sum (f := fun l => (((u k : ℚˣ) : ℚ)⁻¹ * ((u l : ℚˣ) : ℚ)).den +
            ((u k : ℚˣ) : ℚ).den) (fun _ _ => Nat.zero_le _) (mem_univ l)).trans
          (Finset.single_le_sum (f := fun k => ∑ l, ((((u k : ℚˣ) : ℚ)⁻¹ *
            ((u l : ℚˣ) : ℚ)).den + ((u k : ℚˣ) : ℚ).den)) (fun _ _ => Nat.zero_le _) (mem_univ k))
      have hnd : ∀ v : ℕ, 0 < v → v ≤ bound → ¬ P n ∣ v := fun v hv hvb hdv => by
        have := Nat.le_of_dvd hv hdv
        have := hPge n
        omega
      have he : ¬ ((P n : ℕ) : ℤ) ∣ ((j' : ℕ) : ℤ) - (j : ℕ) := by
        intro hdv
        have hlt : |((j' : ℕ) : ℤ) - (j : ℕ)| < P n := by
          rw [abs_lt]; constructor <;> omega
        have hne' : ((j' : ℕ) : ℤ) - (j : ℕ) ≠ 0 := fun h0 => hjj (Fin.ext (by omega))
        have := Int.le_of_dvd (abs_pos.mpr hne') ((dvd_abs _ _).mpr hdv)
        omega
      have hcast : ((j' : ℚ) - j) = ((((j' : ℕ) : ℤ) - (j : ℕ) : ℤ) : ℚ) := by push_cast; ring
      rw [hcast] at h1
      exact den_ne_one_of_prime_mul (hP n) (u k : ℚˣ).ne_zero
        (hnd _ (Rat.den_pos _) (by omega)) (hnd _ (Rat.den_pos _) (by omega)) he h1
  -- the spread vector reproduces the compressed matrix
  have hquad : ∀ n, ∀ β : Fin M → ℂ, hermQuad (gram φ (spreadFamily (P n) u))
      (fun p => β p.2 / (P n : ℂ)) = hermQuad (A n) β := by
    intro n β
    have hPn : (P n : ℂ) ≠ 0 := by exact_mod_cast (hP n).pos.ne'
    simp only [hermQuad_gram]
    have hA : hermQuad (A n) β = (∑ k, ∑ l, conj (β k) * (s ((u k)⁻¹ * u l) +
        (((1 : ℝ) / P n : ℝ) : ℂ) * ψD ((u k)⁻¹ * u l)) * β l).re := by
      rw [show hermQuad (A n) β = hermQuad (gram (fun v => s v + (((1 : ℝ) / P n : ℝ) : ℂ) *
        ψD v) u) β from by congr 1]
      rw [hermQuad_gram]
    rw [hA]
    congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, hentry]
    -- reorder to `Σ_k Σ_l Σ_j Σ_j'`
    rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    simp_rw [Finset.sum_comm (s := (univ : Finset (Fin (P n)))) (t := (univ : Finset (Fin M)))]
    refine sum_congr rfl fun l _ => ?_
    have e : ∀ j j' : Fin (P n), conj (β k / (P n : ℂ)) *
        (s ((u k)⁻¹ * u l) + if j = j' then ψD ((u k)⁻¹ * u l) else 0) * (β l / (P n : ℂ)) =
        conj (β k) * β l / ((P n : ℂ) * P n) * s ((u k)⁻¹ * u l) +
          if j = j' then conj (β k) * β l / ((P n : ℂ) * P n) * ψD ((u k)⁻¹ * u l) else 0 := by
      intro j j'
      rw [map_div₀, Complex.conj_natCast]
      split_ifs <;> ring
    simp_rw [e, sum_add_distrib, Finset.sum_ite_eq, if_pos (mem_univ _), sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  -- lower semicontinuity along the primes
  have hlim : Tendsto (fun n => ((1 : ℝ) / P n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => by positivity) fun n => ?_
    have := hPge n
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : n + 1 ≤ P n))
  have hconv : ∀ a b, Tendsto (fun n => A n a b) atTop (𝓝 (gram s u a b)) := by
    intro a b
    have : Tendsto (fun n => gram s u a b + (((1 : ℝ) / P n : ℝ) : ℂ) * gram ψD u a b) atTop
        (𝓝 (gram s u a b + ((0 : ℝ) : ℂ) * gram ψD u a b)) :=
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).comp hlim |>.mul_const _)
    simpa [A] using this
  obtain ⟨n, hn⟩ := (eventually_le_hermNegIndex (gram_isHermitian hs u) hconv).exists
  let S : (Fin M → ℂ) →ₗ[ℂ] (Fin (P n) × Fin M → ℂ) :=
    { toFun := fun β p => β p.2 / (P n : ℂ)
      map_add' := fun β β' => funext fun p => by simp [add_div]
      map_smul' := fun t β => funext fun p => by simp [mul_div_assoc] }
  have hle := hermNegIndex_le_of_hermQuad_eq (A n) (gram φ (spreadFamily (P n) u)) S
    fun β => hquad n β
  exact (Nat.cast_le.mpr (hn.trans hle)).trans (hermNegIndex_gram_le_negIndex _ _)

/-! ### No continuous dilation part -/

/-- **No continuous dilation part.** Let `ψ` be positive, Hecke-supported and carry the integer
successor. If the dilation part `s + ψ ∘ dilation` of `s(|a|) + ψ` is continuous at `1`, the state
has infinitely many negative squares. -/
theorem negIndex_slope_add_eq_top {s : posUnits → ℂ} (hs : IsHermKernel s)
    {ψ : AffineGroupQ → ℂ} (hψ : IsPosDefOnGroup ψ) (hψH : IsHeckeSupported ψ)
    (hsucc : HasIntegerSuccessor ψ)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ u : posUnits, |((u : ℚˣ) : ℚ) - 1| < δ →
      ‖(s u + ψ (dilation (u : ℚˣ))) - (s 1 + ψ (dilation ((1 : posUnits) : ℚˣ)))‖ < ε) :
    negIndex (fun g => s (slopeAbs g) + ψ g) = ⊤ := by
  refine top_le_iff.mp ((top_le_iff.mpr ?_).trans (negIndex_le_negIndex_slope_add hs hψH))
  have e : s = fun u => (s u + ψ (dilation (u : ℚˣ))) - ψ (dilation (u : ℚˣ)) :=
    funext fun u => by ring
  rw [e]
  have hψ1 : ψ (dilation ((1 : posUnits) : ℚˣ)) = ((1 : ℝ) : ℂ) := by
    have := hsucc 0
    rw [translation_zero, Rat.den_zero, if_pos rfl] at this
    rw [OneMemClass.coe_one, map_one, this, Complex.ofReal_one]
  refine negIndex_sub_eq_top hcont (fun ε hε => ?_) one_pos hψ1
  -- the successor law makes `ψ` decay with the denominator
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
  refine ⟨N, fun u hu => ?_⟩
  have hlaw := normSq_dilation_le hψ hsucc (u : ℚˣ)
  have hden : (N : ℝ) ≤ ((u : ℚˣ) : ℚ).den := by exact_mod_cast hu
  have hnum : (1 : ℝ) ≤ (((u : ℚˣ) : ℚ).num.natAbs : ℝ) := by
    have := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (u : ℚˣ).ne_zero)
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hsq : ‖ψ (dilation (u : ℚˣ))‖ ^ 2 < ε ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    have h1 : (N : ℝ) * Complex.normSq (ψ (dilation (u : ℚˣ))) ≤ 1 := by
      calc (N : ℝ) * Complex.normSq (ψ (dilation (u : ℚˣ)))
          ≤ ((((u : ℚˣ) : ℚ).num.natAbs : ℝ) * ((u : ℚˣ) : ℚ).den) *
            Complex.normSq (ψ (dilation (u : ℚˣ))) := by
            gcongr
            · exact Complex.normSq_nonneg _
            · nlinarith
        _ ≤ 1 := hlaw
    have h2 : 1 / ε ^ 2 * Complex.normSq (ψ (dilation (u : ℚˣ))) < 1 ∨
        Complex.normSq (ψ (dilation (u : ℚˣ))) = 0 := by
      rcases (Complex.normSq_nonneg (ψ (dilation (u : ℚˣ)))).eq_or_lt with h | h
      · exact Or.inr h.symm
      · exact Or.inl (lt_of_lt_of_le (by gcongr) h1)
    rcases h2 with h2 | h2
    · rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)] at h2
      exact h2
    · rw [h2]; positivity
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- **Weil's correlation cannot be the dilation part of a slope correction of a positive
Hecke-supported state with the integer successor**, at any finite index. -/
theorem negIndex_eq_top_of_weil_slope_add {s : posUnits → ℂ} (hs : IsHermKernel s)
    {ψ : AffineGroupQ → ℂ} (hψ : IsPosDefOnGroup ψ) (hψH : IsHeckeSupported ψ)
    (hsucc : HasIntegerSuccessor ψ) (hdil : ∀ u : posUnits, s u + ψ (dilation (u : ℚˣ)) = ratCorr u) :
    negIndex (fun g => s (slopeAbs g) + ψ g) = ⊤ := by
  refine negIndex_slope_add_eq_top hs hψ hψH hsucc fun ε hε => ?_
  simp_rw [hdil]
  -- continuity of `r ↦ splineCorr (−log r)` at `1`
  have hc : ContinuousAt (fun x : ℝ => splineCorr (-Real.log x)) 1 :=
    (continuous_splineCorr.continuousAt).comp ((Real.continuousAt_log one_ne_zero).neg)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨δ', hδ'0, hδ'δ⟩ := exists_rat_btwn hδ
  refine ⟨δ', by exact_mod_cast hδ'0, fun u hu => ?_⟩
  have hdist : dist (((u : ℚˣ) : ℚ) : ℝ) 1 < δ := by
    rw [Real.dist_eq]
    have e : |(((u : ℚˣ) : ℚ) : ℝ) - 1| = ((|((u : ℚˣ) : ℚ) - 1| : ℚ) : ℝ) := by push_cast; rfl
    rw [e]
    exact lt_trans (by exact_mod_cast hu) hδ'δ
  have h := hδε hdist
  rw [dist_eq_norm] at h
  simpa [ratCorr, logPos] using h

end GaloisForLFunctions.AdelicKreinGeometry
