import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Product estimates for separated nodes

Elementary estimates used to bound Lagrange basis denominators over nodes
with a gap lower bound:

* telescoping: points with consecutive gaps `≥ η` spread linearly in the
  index distance, `η·|i - j| ≤ |pts i - pts j|`;
* the real product identity `∏_{j<n} (n - j) = n!`;
* the binomial pair bound `n!/2^n ≤ i!·(n-i)!` for `i ≤ n`.

Combined, these give the crude Lagrange denominator bound
`∏_{j ≠ i} |pts i - pts j| ≥ η^n · n!/2^n`, exponentially sharp enough for
limsup-type sampling arguments.
-/

noncomputable section

namespace HTGeometry

open Finset

/-- Telescoped gap bound in coordinate form. -/
theorem gap_telescope {m : ℕ} {pts : Fin (m + 1) → ℝ} {η : ℝ}
    (hgap : ∀ i : Fin m, η ≤ pts i.succ - pts i.castSucc) :
    ∀ (d a : ℕ) (h : a + d ≤ m),
      η * d ≤ pts ⟨a + d, Nat.lt_succ_of_le h⟩ - pts ⟨a, by omega⟩ := by
  intro d
  induction d with
  | zero =>
    intro a h
    simp
  | succ d ihd =>
    intro a h
    have h' : a + d ≤ m := by omega
    have hmid := ihd a h'
    have hstep : η ≤ pts ⟨a + d + 1, by omega⟩ - pts ⟨a + d, by omega⟩ := by
      have := hgap ⟨a + d, by omega⟩
      simpa [Fin.succ_mk, Fin.castSucc_mk] using this
    have hpts : pts ⟨a + (d + 1), Nat.lt_succ_of_le h⟩
        = pts ⟨a + d + 1, by omega⟩ := rfl
    rw [hpts]
    push_cast
    linarith

/-- Telescoped gap bound between arbitrary ordered indices, real form. -/
theorem sep_sub_le {m : ℕ} {pts : Fin (m + 1) → ℝ} {η : ℝ}
    (hgap : ∀ i : Fin m, η ≤ pts i.succ - pts i.castSucc)
    {i j : Fin (m + 1)} (hij : (i : ℕ) ≤ (j : ℕ)) :
    η * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ pts j - pts i := by
  have h := gap_telescope hgap ((j : ℕ) - (i : ℕ)) (i : ℕ) (by omega)
  have hj : (⟨(i : ℕ) + ((j : ℕ) - (i : ℕ)),
      Nat.lt_succ_of_le (by omega)⟩ : Fin (m + 1)) = j := by
    apply Fin.ext
    simp only []
    omega
  have hi : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i := Fin.eta i _
  rw [hj, hi] at h
  calc η * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))
      = η * ((((j : ℕ) - (i : ℕ) : ℕ)) : ℝ) := by
        rw [Nat.cast_sub hij]
    _ ≤ pts j - pts i := h

/-- Separated points spread linearly with the index distance. -/
theorem sep_mul_index_dist_le {m : ℕ} {pts : Fin (m + 1) → ℝ} {η : ℝ}
    (hη : 0 ≤ η)
    (hgap : ∀ i : Fin m, η ≤ pts i.succ - pts i.castSucc)
    (i j : Fin (m + 1)) :
    η * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ |pts i - pts j| := by
  rcases le_total (i : ℕ) (j : ℕ) with hij | hij
  · have h := sep_sub_le hgap hij
    have hnn : (0:ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
      linarith
    have hpts : 0 ≤ pts j - pts i := le_trans (mul_nonneg hη hnn) h
    rw [abs_sub_comm ((i : ℕ) : ℝ), abs_of_nonneg hnn,
      abs_sub_comm (pts i), abs_of_nonneg hpts]
    exact h
  · have h := sep_sub_le hgap hij
    have hnn : (0:ℝ) ≤ ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
      have : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hij
      linarith
    have hpts : 0 ≤ pts i - pts j := le_trans (mul_nonneg hη hnn) h
    rw [abs_of_nonneg hnn, abs_of_nonneg hpts]
    exact h

/-- Real form of the falling product: `∏_{j<n} (n - j) = n!`. -/
theorem prod_range_sub_eq_factorial :
    ∀ n : ℕ, (∏ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ)))
      = (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [Finset.prod_range_succ']
    have h1 : (∏ j ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)))
        = ∏ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j _
      push_cast
      ring
    calc (∏ j ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)))
          * (((n + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ))
        = (∏ j ∈ Finset.range n, ((n : ℝ) - (j : ℝ))) * ((n : ℝ) + 1) := by
          rw [h1]
          push_cast
          ring
      _ = ((n.factorial : ℝ)) * ((n : ℝ) + 1) := by rw [ihn]
      _ = ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring

/-- Binomial pair bound: `n!/2^n ≤ i!·(n-i)!` for `i ≤ n`. -/
theorem factorial_div_two_pow_le {n i : ℕ} (h : i ≤ n) :
    (n.factorial : ℝ) / 2 ^ n
      ≤ (i.factorial : ℝ) * ((n - i).factorial : ℝ) := by
  have hchoose : n.choose i ≤ 2 ^ n := by
    calc n.choose i ≤ ∑ k ∈ Finset.range (n + 1), n.choose k :=
          Finset.single_le_sum (fun k _ => Nat.zero_le _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le h))
      _ = 2 ^ n := Nat.sum_range_choose n
  have hfact : n.choose i * i.factorial * (n - i).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial h
  have hchoose_pos : 0 < n.choose i := Nat.choose_pos h
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
  have hcast : (n.factorial : ℝ)
      = (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) := by
    exact_mod_cast hfact.symm
  rw [hcast]
  have h2 : (n.choose i : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hchoose
  calc (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ)
      ≤ (2 : ℝ) ^ n * (i.factorial : ℝ) * ((n - i).factorial : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (by positivity))
          (by positivity)
    _ = (i.factorial : ℝ) * ((n - i).factorial : ℝ) * 2 ^ n := by ring

/-- Products over an erased node reindex through the ordered enumeration. -/
theorem prod_erase_enum {N : ℕ} {s : Finset ℝ} (hcard : s.card = N + 1)
    (i₀ : Fin (N + 1)) (g : ℝ → ℝ) :
    ∏ u ∈ s.erase ((s.orderIsoOfFin hcard i₀ : ℝ)), g u
      = ∏ j ∈ Finset.univ.erase i₀, g ((s.orderIsoOfFin hcard j : ℝ)) := by
  symm
  apply Finset.prod_bij
    (i := fun (j : Fin (N + 1)) (_ : j ∈ Finset.univ.erase i₀) =>
      ((s.orderIsoOfFin hcard j : ℝ)))
  · intro j hj
    rw [Finset.mem_erase] at hj ⊢
    refine ⟨?_, (s.orderIsoOfFin hcard j).2⟩
    intro heq
    apply hj.1
    have hinj : (s.orderIsoOfFin hcard j : ℝ)
        = (s.orderIsoOfFin hcard i₀ : ℝ) := heq
    have := Subtype.coe_injective hinj
    exact (s.orderIsoOfFin hcard).injective this
  · intro j₁ hj₁ j₂ hj₂ heq
    exact (s.orderIsoOfFin hcard).injective (Subtype.coe_injective heq)
  · intro u hu
    rw [Finset.mem_erase] at hu
    refine ⟨(s.orderIsoOfFin hcard).symm ⟨u, hu.2⟩, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro heq
      apply hu.1
      have := congrArg (fun z => ((s.orderIsoOfFin hcard z : ℝ))) heq
      simpa using this
    · simp
  · intro j hj
    rfl

/-- The erased index-distance product is a factorial pair. -/
theorem prod_erase_index_dist (N : ℕ) (i₀ : Fin (N + 1)) :
    ∏ j ∈ Finset.univ.erase i₀, |((i₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
      = (((i₀ : ℕ)).factorial : ℝ) * ((N - (i₀ : ℕ)).factorial : ℝ) := by
  have hsplit : Finset.univ.erase i₀
      = (Finset.univ.filter fun j : Fin (N + 1) => (j : ℕ) < (i₀ : ℕ))
        ∪ (Finset.univ.filter fun j : Fin (N + 1) => (i₀ : ℕ) < (j : ℕ)) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, and_true, ne_eq]
    rw [Fin.ext_iff]
    omega
  have hdisj : Disjoint
      (Finset.univ.filter fun j : Fin (N + 1) => (j : ℕ) < (i₀ : ℕ))
      (Finset.univ.filter fun j : Fin (N + 1) => (i₀ : ℕ) < (j : ℕ)) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    rw [Finset.mem_filter] at hj₁ hj₂
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hbelow : (∏ j ∈ Finset.univ.filter
        fun j : Fin (N + 1) => (j : ℕ) < (i₀ : ℕ),
        |((i₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)
      = (((i₀ : ℕ)).factorial : ℝ) := by
    rw [← prod_range_sub_eq_factorial (i₀ : ℕ)]
    apply Finset.prod_bij
      (i := fun (j : Fin (N + 1)) (_ : j ∈ _) => (j : ℕ))
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact Finset.mem_range.2 hj.2
    · intro j₁ _ j₂ _ heq
      exact Fin.ext heq
    · intro v hv
      rw [Finset.mem_range] at hv
      have hvN : v < N + 1 := by
        have := i₀.isLt
        omega
      exact ⟨⟨v, hvN⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, rfl⟩
    · intro j hj
      rw [Finset.mem_filter] at hj
      rw [abs_of_pos]
      have : ((j : ℕ) : ℝ) < ((i₀ : ℕ) : ℝ) := by exact_mod_cast hj.2
      linarith
  have habove : (∏ j ∈ Finset.univ.filter
        fun j : Fin (N + 1) => (i₀ : ℕ) < (j : ℕ),
        |((i₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)
      = ((N - (i₀ : ℕ)).factorial : ℝ) := by
    have hfact : ((N - (i₀ : ℕ)).factorial : ℝ)
        = ∏ v ∈ Finset.range (N - (i₀ : ℕ)), ((v : ℝ) + 1) := by
      rw [Nat.factorial_eq_prod_range_add_one]
      push_cast
      rfl
    rw [hfact]
    apply Finset.prod_bij
      (i := fun (j : Fin (N + 1)) (hj : j ∈ _) => (j : ℕ) - (i₀ : ℕ) - 1)
    · intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_range]
      have := j.isLt
      omega
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_filter] at hj₁ hj₂
      apply Fin.ext
      omega
    · intro v hv
      rw [Finset.mem_range] at hv
      have hlt : (i₀ : ℕ) + v + 1 < N + 1 := by
        have := i₀.isLt
        omega
      refine ⟨⟨(i₀ : ℕ) + v + 1, hlt⟩, Finset.mem_filter.2
        ⟨Finset.mem_univ _, by simp⟩, ?_⟩
      show ((i₀ : ℕ) + v + 1) - (i₀ : ℕ) - 1 = v
      omega
    · intro j hj
      rw [Finset.mem_filter] at hj
      have hlt : ((i₀ : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hj.2
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      have hle1 : (i₀ : ℕ) ≤ (j : ℕ) := by omega
      have hle2 : 1 ≤ (j : ℕ) - (i₀ : ℕ) := by omega
      rw [Nat.cast_sub hle2, Nat.cast_sub hle1]
      push_cast
      ring
  rw [hbelow, habove]

/-- **Crude Lagrange denominator bound** for `η`-separated nodes:
`∏_{u ≠ t} |t - u| ≥ η^N · N!/2^N`. -/
theorem prod_erase_abs_sub_ge
    {s : Finset ℝ} {N : ℕ} (hcard : s.card = N + 1) {η : ℝ} (hη : 0 ≤ η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {t : ℝ} (ht : t ∈ s) :
    η ^ N * ((N.factorial : ℝ) / 2 ^ N) ≤ ∏ u ∈ s.erase t, |t - u| := by
  set e := s.orderIsoOfFin hcard with he
  set i₀ : Fin (N + 1) := e.symm ⟨t, ht⟩ with hi₀
  have hti₀ : ((e i₀ : ℝ)) = t := by
    rw [hi₀]
    simp
  have hgap : ∀ i : Fin N, η ≤ ((e i.succ : ℝ)) - ((e i.castSucc : ℝ)) := by
    intro i
    have hlt : ((e i.castSucc : ℝ)) < ((e i.succ : ℝ)) := by
      exact_mod_cast e.strictMono Fin.castSucc_lt_succ
    have hne : ((e i.succ : ℝ)) ≠ ((e i.castSucc : ℝ)) := ne_of_gt hlt
    have h := hsep _ (e i.succ).2 _ (e i.castSucc).2 hne
    rwa [abs_of_pos (by linarith)] at h
  rw [← hti₀, prod_erase_enum hcard i₀ (fun u => |((e i₀ : ℝ)) - u|)]
  have hterm : ∀ j ∈ Finset.univ.erase i₀,
      η * |((i₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ |((e i₀ : ℝ)) - ((e j : ℝ))| :=
    fun j _ => sep_mul_index_dist_le (pts := fun i => ((e i : ℝ))) hη hgap i₀ j
  calc η ^ N * ((N.factorial : ℝ) / 2 ^ N)
      ≤ η ^ N * ((((i₀ : ℕ)).factorial : ℝ)
          * ((N - (i₀ : ℕ)).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (factorial_div_two_pow_le i₀.is_le)
          (by positivity)
    _ = ∏ j ∈ Finset.univ.erase i₀,
          (η * |((i₀ : ℕ) : ℝ) - ((j : ℕ) : ℝ)|) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, prod_erase_index_dist,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
        norm_num
    _ ≤ ∏ j ∈ Finset.univ.erase i₀, |((e i₀ : ℝ)) - ((e j : ℝ))| :=
        Finset.prod_le_prod (fun j _ => mul_nonneg hη (abs_nonneg _)) hterm

end HTGeometry
