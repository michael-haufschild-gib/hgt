import GaloisForLFunctions.RHTower.Sieve.RamareLadderErrorSharp

/-!
# The mean square of a power of a prime block times a cofactor polynomial

For a set `B` of primes in `[S_min, B_max]`, a coefficient sequence `|c_m| ≤ 1` on cofactors
`m ≤ X`, and `ℓ ≥ 0`,

`∫_{|w| ≤ W} ‖Q_B(w)^ℓ · C(w)‖² ≤ (5π/2·W + 5e/2·B_max^ℓ X) · X · #B^ℓ (#B + ℓ B_max)^ℓ / S_min^ℓ`,

where `Q_B(w) = ∑_{p ∈ B} μ(p) p^{2πiw}` and `C(w) = ∑_m c_m m^{2πiw}`.

The product is a Dirichlet polynomial indexed by pairs `(g, m)`, `g ∈ B^ℓ`, with value
`(∏ g_i)·m`.  Its fibre energy is at most the number of coincidences `∏g'·m' = ∏g·m`; for fixed
`g, g'` these force `∏g'/gcd(∏g', ∏g) ∣ m`, so there are at most `X·gcd(∏g', ∏g)/∏g'` of them.
Finally `gcd(a, ∏ g_i) ≤ ∏ gcd(a, g_i)` and a product of `ℓ` primes has at most `ℓ` prime
divisors in `B`.  This is the moment computation behind the amplification step of
Matomäki–Radziwiłł; it needs no Euler product.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `b ∣ a·m` forces `b/gcd(b,a) ∣ m`. -/
theorem div_gcd_dvd_of_dvd_mul {a b m : ℕ} (hb : 0 < b) (h : b ∣ a * m) :
    b / Nat.gcd b a ∣ m := by
  have hg : 0 < Nat.gcd b a := Nat.gcd_pos_of_pos_left a hb
  have hc := Nat.coprime_div_gcd_div_gcd hg
  set g := Nat.gcd b a with hgdef
  obtain ⟨b1, hb1⟩ := Nat.gcd_dvd_left b a
  obtain ⟨a1, ha1⟩ := Nat.gcd_dvd_right b a
  rw [← hgdef] at hb1 ha1
  have eb : b / g = b1 := by
    have : b / g = g * b1 / g := by rw [← hb1]
    rw [this]; exact Nat.mul_div_cancel_left b1 hg
  have ea : a / g = a1 := by
    have : a / g = g * a1 / g := by rw [← ha1]
    rw [this]; exact Nat.mul_div_cancel_left a1 hg
  rw [eb, ea] at hc
  rw [eb]
  have h2 : g * b1 ∣ g * (a1 * m) := by
    rw [← hb1, ← mul_assoc, ← ha1]; exact h
  exact hc.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg h2)

/-- The multiples of `d ≥ 1` in a set of integers of `[1, X]` number at most `X/d`. -/
theorem card_filter_dvd_le {D : Finset ℕ} {X : ℕ} (hD : ∀ m ∈ D, 1 ≤ m ∧ m ≤ X) {d : ℕ}
    (hd : 1 ≤ d) : ((D.filter fun m => d ∣ m).card : ℝ) ≤ (X : ℝ) / d := by
  classical
  have hsub : D.filter (fun m => d ∣ m) ⊆ (Finset.Icc 1 X).filter fun m => d ∣ m := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨Finset.mem_Icc.mpr (hD m hm.1), hm.2⟩
  have h := sum_filter_dvd_eq (M := X) hd (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, add_tsub_cancel_right] at h
  calc ((D.filter fun m => d ∣ m).card : ℝ)
      ≤ (((Finset.Icc 1 X).filter fun m => d ∣ m).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((X / d : ℕ) : ℝ) := h
    _ ≤ (X : ℝ) / d := Nat.cast_div_le

/-- `gcd(a, ∏ f_i) ≤ ∏ gcd(a, f_i)` for `a > 0`. -/
theorem gcd_prod_le_prod_gcd {ι : Type*} (s : Finset ι) (f : ι → ℕ) {a : ℕ} (ha : 0 < a) :
    Nat.gcd a (∏ i ∈ s, f i) ≤ ∏ i ∈ s, Nat.gcd a (f i) := by
  classical
  have hpos : ∀ t : Finset ι, 0 < ∏ i ∈ t, Nat.gcd a (f i) := fun t =>
    Finset.prod_pos fun i _ => Nat.gcd_pos_of_pos_left _ ha
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hdvd : Nat.gcd a (f i * ∏ j ∈ s, f j) ∣ Nat.gcd a (f i) * Nat.gcd a (∏ j ∈ s, f j) :=
      gcd_mul_dvd_mul_gcd a (f i) (∏ j ∈ s, f j)
    have h1 := Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ ha)
      (Nat.gcd_pos_of_pos_left _ ha)) hdvd
    exact h1.trans (Nat.mul_le_mul_left _ ih)

/-- The Gallagher phase of a product of positive integers is the product of the phases. -/
theorem prod_unitLogPhase {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 0 < f i)
    (w : ℝ) : ∏ i ∈ s, unitLogPhase w (f i) = unitLogPhase w (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [unitLogPhase]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj),
      unitLogPhase_mul w (hf i (Finset.mem_insert_self i s)).ne'
        (Finset.prod_pos fun j hj => hf j (Finset.mem_insert_of_mem hj)).ne']

/-- **The product as one Dirichlet polynomial over pairs `(g, m)`.** -/
theorem primeBlockPoly_pow_mul_logPoly_eq (B D : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    (hD : ∀ m ∈ D, 0 < m) (c : ℕ → ℂ) (ℓ : ℕ) (w : ℝ) :
    primeBlockPoly B w ^ ℓ * logPoly c D w
      = ∑ t ∈ (Fintype.piFinset fun _ : Fin ℓ => B) ×ˢ D,
          ((∏ i, ((μ (t.1 i) : ℤ) : ℂ)) * c t.2) * unitLogPhase w ((∏ i, t.1 i) * t.2) := by
  classical
  rw [primeBlockPoly, ← Fin.prod_const, Finset.prod_univ_sum, logPoly_eq_sum_mul_unitLogPhase,
    Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun m hm => ?_
  have hgB : ∀ i, g i ∈ B := Fintype.mem_piFinset.mp hg
  have hgpos : ∀ i ∈ (Finset.univ : Finset (Fin ℓ)), 0 < g i := fun i _ => (hB _ (hgB i)).pos
  simp only [moebiusPhase]
  rw [Finset.prod_mul_distrib, prod_unitLogPhase _ _ hgpos,
    unitLogPhase_mul w (Finset.prod_pos hgpos).ne' (hD m hm).ne']
  ring

/-- **Fibre energy by coincidences.**  With unit-bounded coefficients, the fibre energy is at most
the number of pairs of indices with the same value. -/
theorem sum_normSq_fibre_le_coincidences {ι : Type*} [DecidableEq ι] (I : Finset ι) (ν : ι → ℕ)
    (b : ι → ℂ) (hb : ∀ i ∈ I, ‖b i‖ ≤ 1) :
    ∑ n ∈ I.image ν, ‖∑ i ∈ I with ν i = n, b i‖ ^ (2 : ℕ)
      ≤ ∑ i ∈ I, ((I.filter fun j => ν j = ν i).card : ℝ) := by
  have hfib : ∀ n, ‖∑ i ∈ I with ν i = n, b i‖ ≤ ((I.filter fun j => ν j = n).card : ℝ) := by
    intro n
    calc ‖∑ i ∈ I with ν i = n, b i‖ ≤ ∑ i ∈ I with ν i = n, ‖b i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ I with ν i = n, (1 : ℝ) :=
          Finset.sum_le_sum fun i hi => hb i (Finset.mem_filter.mp hi).1
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc ∑ n ∈ I.image ν, ‖∑ i ∈ I with ν i = n, b i‖ ^ (2 : ℕ)
      ≤ ∑ n ∈ I.image ν, ((I.filter fun j => ν j = n).card : ℝ) ^ (2 : ℕ) :=
        Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hfib n) 2
    _ = ∑ n ∈ I.image ν, ∑ i ∈ I with ν i = n, ((I.filter fun j => ν j = ν i).card : ℝ) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [sq, ← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i ∈ I, ((I.filter fun j => ν j = ν i).card : ℝ) :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ν hi) _

/-- `∑_{p ∈ B} gcd(a, p) ≤ #B + ℓ·B_max` when `a` is a product of `ℓ` primes of `B`. -/
theorem sum_gcd_prod_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {ℓ : ℕ} {g : Fin ℓ → ℕ}
    (hg : ∀ i, g i ∈ B) {Bmax : ℕ} (hmax : ∀ p ∈ B, p ≤ Bmax) :
    ∑ p ∈ B, Nat.gcd (∏ i, g i) p ≤ B.card + ℓ * Bmax := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not B (fun p => p ∣ ∏ i, g i)
    (fun p => Nat.gcd (∏ i, g i) p)
  rw [← hsplit]
  have h1 : ∑ p ∈ B.filter (fun p => p ∣ ∏ i, g i), Nat.gcd (∏ i, g i) p ≤ ℓ * Bmax := by
    have hsub : B.filter (fun p => p ∣ ∏ i, g i) ⊆ Finset.univ.image g := by
      intro p hp
      obtain ⟨hpB, hpd⟩ := Finset.mem_filter.mp hp
      have hpp := hB p hpB
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpd
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        ((Nat.prime_dvd_prime_iff_eq hpp (hB _ (hg i))).mp hi).symm⟩
    have hcard : (B.filter (fun p => p ∣ ∏ i, g i)).card ≤ ℓ :=
      (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
    calc ∑ p ∈ B.filter (fun p => p ∣ ∏ i, g i), Nat.gcd (∏ i, g i) p
        ≤ ∑ _p ∈ B.filter (fun p => p ∣ ∏ i, g i), Bmax :=
          Finset.sum_le_sum fun p hp =>
            (Nat.le_of_dvd (hB p (Finset.mem_filter.mp hp).1).pos (Nat.gcd_dvd_right _ _)).trans
              (hmax p (Finset.mem_filter.mp hp).1)
      _ = (B.filter (fun p => p ∣ ∏ i, g i)).card * Bmax := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ℓ * Bmax := Nat.mul_le_mul_right _ hcard
  have h2 : ∑ p ∈ B.filter (fun p => ¬ p ∣ ∏ i, g i), Nat.gcd (∏ i, g i) p ≤ B.card := by
    calc ∑ p ∈ B.filter (fun p => ¬ p ∣ ∏ i, g i), Nat.gcd (∏ i, g i) p
        = ∑ _p ∈ B.filter (fun p => ¬ p ∣ ∏ i, g i), 1 := by
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨hpB, hpd⟩ := Finset.mem_filter.mp hp
          have hcop : Nat.Coprime p (∏ i, g i) := (Nat.Prime.coprime_iff_not_dvd (hB p hpB)).mpr hpd
          rw [Nat.gcd_comm]; exact hcop
      _ ≤ B.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
          exact Finset.card_filter_le _ _
  omega

/-- **The coincidence count of the pair polynomial.**  Summed over all pairs `(g, m)`, the number
of pairs `(g', m')` with `∏g'·m' = ∏g·m` is at most `#B^ℓ·X·(#B + ℓ B_max)^ℓ / S_min^ℓ`. -/
theorem sum_card_coincidences_le {B D : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {X : ℕ}
    (hD : ∀ m ∈ D, 1 ≤ m ∧ m ≤ X) {Smin : ℝ} (hSmin : 0 < Smin) (hmin : ∀ p ∈ B, Smin ≤ p)
    {Bmax : ℕ} (hmax : ∀ p ∈ B, p ≤ Bmax) (ℓ : ℕ) :
    ∑ t ∈ (Fintype.piFinset fun _ : Fin ℓ => B) ×ˢ D,
        ((((Fintype.piFinset fun _ : Fin ℓ => B) ×ˢ D).filter
          fun s => (∏ i, s.1 i) * s.2 = (∏ i, t.1 i) * t.2).card : ℝ)
      ≤ (B.card : ℝ) ^ ℓ * X * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ / Smin ^ ℓ := by
  classical
  set G := Fintype.piFinset fun _ : Fin ℓ => B with hG
  have hGB : ∀ g ∈ G, ∀ i, g i ∈ B := fun g hg => Fintype.mem_piFinset.mp hg
  have hGpos : ∀ g ∈ G, 0 < ∏ i, g i := fun g hg =>
    Finset.prod_pos fun i _ => (hB _ (hGB g hg i)).pos
  -- a coincidence is determined by its prime tuple
  have hstep : ∀ t ∈ G ×ˢ D, ((G ×ˢ D).filter fun s => (∏ i, s.1 i) * s.2 = (∏ i, t.1 i) * t.2).card
      ≤ (G.filter fun g' => (∏ i, g' i) ∣ (∏ i, t.1 i) * t.2).card := by
    intro t _
    refine Finset.card_le_card_of_injOn (fun s => s.1) (fun s hs => ?_) (fun s hs s' hs' h => ?_)
    · obtain ⟨hsI, hse⟩ := Finset.mem_filter.mp hs
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨(Finset.mem_product.mp hsI).1, hse ▸ dvd_mul_right _ _⟩
    · obtain ⟨hsI, hse⟩ := Finset.mem_filter.mp hs
      obtain ⟨hsI', hse'⟩ := Finset.mem_filter.mp hs'
      simp only at h
      have hpos := hGpos _ (Finset.mem_product.mp hsI').1
      have h2 : s.2 = s'.2 := by
        rw [h] at hse
        exact Nat.eq_of_mul_eq_mul_left hpos (hse.trans hse'.symm)
      exact Prod.ext h h2
  -- reorganise the double count
  have hswap : ∑ t ∈ G ×ˢ D, (G.filter fun g' => (∏ i, g' i) ∣ (∏ i, t.1 i) * t.2).card
      = ∑ g' ∈ G, ∑ g ∈ G, (D.filter fun m => (∏ i, g' i) ∣ (∏ i, g i) * m).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_product]
    calc _ = ∑ g ∈ G, ∑ g' ∈ G, ∑ m ∈ D,
          (if (∏ i, g' i) ∣ (∏ i, g i) * m then 1 else 0) :=
          Finset.sum_congr rfl fun g _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  -- one prime tuple `g'`
  have hone : ∀ g' ∈ G, (∑ g ∈ G, ((D.filter fun m => (∏ i, g' i) ∣ (∏ i, g i) * m).card : ℝ))
      ≤ (X : ℝ) * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ / Smin ^ ℓ := by
    intro g' hg'
    set a := ∏ i, g' i with ha
    have ha0 : 0 < a := hGpos g' hg'
    have hterm : ∀ g ∈ G, ((D.filter fun m => a ∣ (∏ i, g i) * m).card : ℝ)
        ≤ (X : ℝ) * (Nat.gcd a (∏ i, g i) : ℝ) / a := by
      intro g _
      set d := a / Nat.gcd a (∏ i, g i) with hd
      have hgcd0 : 0 < Nat.gcd a (∏ i, g i) := Nat.gcd_pos_of_pos_left _ ha0
      have hd1 : 1 ≤ d := Nat.div_pos (Nat.gcd_le_left _ ha0) hgcd0
      have hsub : D.filter (fun m => a ∣ (∏ i, g i) * m) ⊆ D.filter fun m => d ∣ m := by
        intro m hm
        rw [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1, div_gcd_dvd_of_dvd_mul ha0 hm.2⟩
      have hcast : (d : ℝ) = (a : ℝ) / (Nat.gcd a (∏ i, g i) : ℝ) := by
        rw [hd, Nat.cast_div (Nat.gcd_dvd_left _ _) (by exact_mod_cast hgcd0.ne')]
      calc ((D.filter fun m => a ∣ (∏ i, g i) * m).card : ℝ)
          ≤ ((D.filter fun m => d ∣ m).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ (X : ℝ) / d := card_filter_dvd_le hD hd1
        _ = (X : ℝ) * (Nat.gcd a (∏ i, g i) : ℝ) / a := by
            rw [hcast]
            have : (0 : ℝ) < Nat.gcd a (∏ i, g i) := by exact_mod_cast hgcd0
            field_simp
    have hgcdsum : (∑ g ∈ G, (Nat.gcd a (∏ i, g i) : ℝ)) ≤ ((B.card : ℝ) + ℓ * Bmax) ^ ℓ := by
      have h1 : ∀ g ∈ G, (Nat.gcd a (∏ i, g i) : ℝ) ≤ ∏ i, (Nat.gcd a (g i) : ℝ) := by
        intro g _
        have := gcd_prod_le_prod_gcd Finset.univ g ha0
        exact_mod_cast this
      have h2 : ∑ g ∈ G, ∏ i, (Nat.gcd a (g i) : ℝ) = (∑ p ∈ B, (Nat.gcd a p : ℝ)) ^ ℓ := by
        rw [hG, ← Fin.prod_const]
        exact (Finset.prod_univ_sum (fun _ : Fin ℓ => B) (fun _ p => (Nat.gcd a p : ℝ))).symm
      have h3 : (∑ p ∈ B, (Nat.gcd a p : ℝ)) ≤ (B.card : ℝ) + ℓ * Bmax := by
        have := sum_gcd_prod_le hB (hGB g' hg') hmax
        rw [← ha] at this
        exact_mod_cast this
      calc (∑ g ∈ G, (Nat.gcd a (∏ i, g i) : ℝ)) ≤ ∑ g ∈ G, ∏ i, (Nat.gcd a (g i) : ℝ) :=
            Finset.sum_le_sum h1
        _ = _ := h2
        _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) h3 ℓ
    have hamin : Smin ^ ℓ ≤ (a : ℝ) := by
      rw [ha]
      push_cast
      calc Smin ^ ℓ = ∏ _i : Fin ℓ, Smin := by rw [Fin.prod_const]
        _ ≤ ∏ i, (g' i : ℝ) :=
            Finset.prod_le_prod (fun _ _ => hSmin.le) fun i _ => hmin _ (hGB g' hg' i)
    have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    calc (∑ g ∈ G, ((D.filter fun m => a ∣ (∏ i, g i) * m).card : ℝ))
        ≤ ∑ g ∈ G, (X : ℝ) * (Nat.gcd a (∏ i, g i) : ℝ) / a := Finset.sum_le_sum hterm
      _ = (X : ℝ) / a * ∑ g ∈ G, (Nat.gcd a (∏ i, g i) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by ring
      _ ≤ (X : ℝ) / a * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ :=
          mul_le_mul_of_nonneg_left hgcdsum (by positivity)
      _ ≤ (X : ℝ) / Smin ^ ℓ * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ := by
          gcongr
      _ = _ := by ring
  have hcardG : (G.card : ℝ) = (B.card : ℝ) ^ ℓ := by
    rw [hG, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast; ring
  calc ∑ t ∈ G ×ˢ D, (((G ×ˢ D).filter
          fun s => (∏ i, s.1 i) * s.2 = (∏ i, t.1 i) * t.2).card : ℝ)
      ≤ ∑ t ∈ G ×ˢ D, ((G.filter fun g' => (∏ i, g' i) ∣ (∏ i, t.1 i) * t.2).card : ℝ) :=
        Finset.sum_le_sum fun t ht => by exact_mod_cast hstep t ht
    _ = ∑ g' ∈ G, ∑ g ∈ G, ((D.filter fun m => (∏ i, g' i) ∣ (∏ i, g i) * m).card : ℝ) := by
        exact_mod_cast hswap
    _ ≤ ∑ _g' ∈ G, (X : ℝ) * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ / Smin ^ ℓ := Finset.sum_le_sum hone
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardG]; ring

/-- **The moment computation.**  `∫_{|w| ≤ W} ‖Q_B^ℓ C‖² ≤ (5π/2·W + 5e/2·B_max^ℓ X)·
#B^ℓ X (#B + ℓB_max)^ℓ / S_min^ℓ`. -/
theorem integral_normSq_primeBlockPoly_pow_mul_logPoly_le {B D : Finset ℕ}
    (hB : ∀ p ∈ B, p.Prime) {c : ℕ → ℂ} (hc : ∀ m, ‖c m‖ ≤ 1) {X : ℕ}
    (hD : ∀ m ∈ D, 1 ≤ m ∧ m ≤ X) {Smin : ℝ} (hSmin : 0 < Smin) (hmin : ∀ p ∈ B, Smin ≤ p)
    {Bmax : ℕ} (hmax : ∀ p ∈ B, p ≤ Bmax) (ℓ : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖primeBlockPoly B w ^ ℓ * logPoly c D w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * X : ℕ) : ℝ))
          * ((B.card : ℝ) ^ ℓ * X * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ / Smin ^ ℓ) := by
  classical
  set G := Fintype.piFinset fun _ : Fin ℓ => B with hG
  have hGB : ∀ g ∈ G, ∀ i, g i ∈ B := fun g hg => Fintype.mem_piFinset.mp hg
  simp_rw [primeBlockPoly_pow_mul_logPoly_eq B D hB (fun m hm => (hD m hm).1) c ℓ]
  have hpos : ∀ t ∈ G ×ˢ D, 0 < (∏ i, t.1 i) * t.2 := by
    intro t ht
    obtain ⟨hg, hm⟩ := Finset.mem_product.mp ht
    exact Nat.mul_pos (Finset.prod_pos fun i _ => (hB _ (hGB _ hg i)).pos) (hD _ hm).1
  have hle : ∀ t ∈ G ×ˢ D, (∏ i, t.1 i) * t.2 ≤ Bmax ^ ℓ * X := by
    intro t ht
    obtain ⟨hg, hm⟩ := Finset.mem_product.mp ht
    refine Nat.mul_le_mul ?_ (hD _ hm).2
    have := Finset.prod_le_pow_card Finset.univ t.1 Bmax fun i _ => hmax _ (hGB _ hg i)
    simpa using this
  have hbase := integral_normSq_sum_unitLogPhase_le (G ×ˢ D) (fun t => (∏ i, t.1 i) * t.2)
    (fun t => (∏ i, ((μ (t.1 i) : ℤ) : ℂ)) * c t.2) hpos hle hW
  have hb : ∀ t ∈ G ×ˢ D, ‖(∏ i, ((μ (t.1 i) : ℤ) : ℂ)) * c t.2‖ ≤ 1 := by
    intro t ht
    obtain ⟨hg, -⟩ := Finset.mem_product.mp ht
    rw [norm_mul, norm_prod]
    have hone : ∏ i, ‖((μ (t.1 i) : ℤ) : ℂ)‖ = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      rw [ArithmeticFunction.moebius_apply_prime (hB _ (hGB _ hg i))]
      simp
    rw [hone, one_mul]
    exact hc _
  have henergy := (sum_normSq_fibre_le_coincidences (G ×ˢ D) (fun t => (∏ i, t.1 i) * t.2)
    (fun t => (∏ i, ((μ (t.1 i) : ℤ) : ℂ)) * c t.2) hb).trans
      (sum_card_coincidences_le hB hD hSmin hmin hmax ℓ)
  have hcoef : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * X : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left henergy hcoef)

end

end RHTower.Sieve
