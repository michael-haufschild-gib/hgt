import GaloisForLFunctions.RHTower.CensusProfile

/-!
# The variation functional and the Stieltjes content of the census profile

The census profile jumps only at the ξ-zero heights, and a jump is `2^k`-invisible to the census
exactly when it is divisible by `2^k`.  The **variation functional** `V k T` counts the heights
below `T` where the jump divisor is NOT `2^k`-divisible — the rung-failing heights.  It is a
monotone integer profile, `0` iff every enclosed jump is `2^k`-divisible, forced to `0` by the rung
certificate, and its failure criterion at each height is decidably testable on the finite carrier
through the transport.

From it two objects on the line:

* **(a) the variation zero-set** `badHeightSet k = {t | ¬ 2^k ∣ discJump t}` — a locally finite,
  closed, discrete subset of ℝ whose emptiness at every level is RH: the boundary target reduced to
  a subset of the line.
* **(b) the Stieltjes content** `censusIncrement k a b = censusProfile k b − censusProfile k a` — a
  finitely additive `ZMod (2^k)`-valued content, atomic on the zero heights with weight
  `censusAtom k t = (discJump t : ZMod (2^k))`, whose finite-carrier counterpart differs by the
  divisor-difference `jumpDiff`, itself `2^k`-valued (so the two contents agree mod `2^k`).
-/

namespace RHTower

open Complex Set Metric Filter Topology

/-! ## The variation functional -/

/-- The rung-failing heights below `T`: box-zero heights whose jump divisor is not `2^k`-divisible. -/
noncomputable def badHeights (k : ℕ) (T : ℝ) : Finset ℝ :=
  ((boxFinset T).image Complex.im).filter (fun t => ¬ (2 ^ k ∣ discJump t))

theorem mem_badHeights {k : ℕ} {T : ℝ} {t : ℝ} :
    t ∈ badHeights k T ↔ (∃ z ∈ boxFinset T, z.im = t) ∧ ¬ (2 ^ k ∣ discJump t) := by
  rw [badHeights, Finset.mem_filter, Finset.mem_image]

/-- **The variation functional**: the number of rung-failing heights below `T`. -/
noncomputable def V (k : ℕ) (T : ℝ) : ℕ := (badHeights k T).card

/-- The rung-failing heights grow with the height window. -/
theorem badHeights_subset {k : ℕ} {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    badHeights k T₁ ⊆ badHeights k T₂ := by
  intro t ht
  rw [mem_badHeights] at ht ⊢
  obtain ⟨⟨z, hz, hzt⟩, hnd⟩ := ht
  exact ⟨⟨z, boxFinset_subset h hz, hzt⟩, hnd⟩

/-- **The variation functional is monotone.** -/
theorem V_mono {k : ℕ} {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : V k T₁ ≤ V k T₂ :=
  Finset.card_le_card (badHeights_subset h)

/-- **The variation vanishes iff every enclosed jump is `2^k`-divisible.** -/
theorem V_eq_zero_iff (k : ℕ) (T : ℝ) :
    V k T = 0 ↔ ∀ z ∈ boxZeros T, 2 ^ k ∣ discJump z.im := by
  rw [V, badHeights, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h z hz
    exact not_not.mp (h (Finset.mem_image_of_mem _ (mem_boxFinset.mpr hz)))
  · intro h t ht
    rw [not_not]
    obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp ht
    rw [← hzt]
    exact h z (mem_boxFinset.mp hz)

/-- **The rung certificate forces the variation to zero.**  If every box zero below `T` has order
divisible by `2^k`, no height is rung-failing. -/
theorem V_eq_zero_of_windowCertificate {k : ℕ} {T : ℝ} (hc : WindowCertificate k T) :
    V k T = 0 := by
  rw [V_eq_zero_iff]
  intro z hz
  exact dvd_discJump_of_windowCertificate hc hz.1.2.2.1 hz.1.2.2.2

/-- **The finite-carrier shadow.**  Under the height-`t` transport data, ξ's rung-failure at height
`t` is decidably testable on the finite carrier: `2^k` divides ξ's jump iff it divides the finite
carrier's jump. -/
theorem dvd_discJump_iff_finiteDiscJump {N k : ℕ} {H : ℝ → Finset ℂ} {mg : ℂ → ℕ} (t : ℝ)
    (hstrip : ∀ z ∈ H t, 0 < z.re ∧ z.re < 1)
    (hmg : ∀ z ∈ H t, (mg z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl : ∀ z ∈ H t, lineReflect z ∈ H t)
    (hD : ∑ z ∈ stripHeightFinset t, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ H t, mg z
        [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ (stripHeightFinset t).filter (fun z => z.re = 1 / 2),
          (analyticOrderAt xi z).toNat
        ≡ ∑ z ∈ (H t).filter (fun z => z.re = 1 / 2), mg z [MOD 2 ^ (k + 1)]) :
    2 ^ k ∣ discJump t ↔ 2 ^ k ∣ finiteDiscJump H mg t := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  have htrans := windowDiscBit_transport (N := N) k
    (fun z _ => ENat.coe_toNat (xi_order_ne_top z))
    (fun z hz => lineReflect_mem_stripHeightFinset hz) hstrip hmg hcl hD hL
  rw [windowDiscBit, windowDiscBit, windowRightSum_stripHeightFinset] at htrans
  rw [← ZMod.natCast_eq_zero_iff (discJump t), ← ZMod.natCast_eq_zero_iff (finiteDiscJump H mg t),
    finiteDiscJump, htrans]

/-! ## (a) The variation zero-set -/

/-- **The variation zero-set** at level `k`: the heights carrying a non-`2^k`-divisible jump. -/
def badHeightSet (k : ℕ) : Set ℝ := {t : ℝ | ¬ (2 ^ k ∣ discJump t)}

/-- A rung-failing height carries a box ξ-zero. -/
theorem boxHeightZeros_nonempty_of_mem_badHeightSet {k : ℕ} {t : ℝ} (ht : t ∈ badHeightSet k) :
    ∃ z ∈ boxHeightZeros t, True := by
  have hne : discJump t ≠ 0 := fun h => ht (h ▸ dvd_zero _)
  obtain ⟨z, hz, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rwa [← discJump])
  exact ⟨z, (Set.Finite.mem_toFinset _).mp hz, trivial⟩

/-- **Local finiteness.**  Only finitely many rung-failing heights lie in any bounded interval: each
carries a box ξ-zero, and those zeros are confined to a ball. -/
theorem badHeightSet_inter_ball_finite (k : ℕ) (x r : ℝ) :
    (badHeightSet k ∩ Metric.ball x r).Finite := by
  classical
  set FS : Finset ℝ := ((xi_zeros_finite_ball 2 (|x| + r + 2)).toFinset.filter
      (fun z => 1 / 2 < z.re ∧ z.re < 1)).image Complex.im with hFS
  apply Set.Finite.subset (FS.finite_toSet)
  intro t ht
  obtain ⟨htbad, htball⟩ := ht
  obtain ⟨z, hz, -⟩ := boxHeightZeros_nonempty_of_mem_badHeightSet htbad
  obtain ⟨h1, h2, him, hz0⟩ := hz
  have htlt : |t| < |x| + r := by
    rw [mem_ball, Real.dist_eq] at htball
    obtain ⟨hlo, hhi⟩ := abs_lt.mp htball
    rw [abs_lt]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [hFS, Finset.mem_coe, Finset.mem_image]
  refine ⟨z, ?_, him⟩
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  refine ⟨⟨?_, hz0⟩, h1, h2⟩
  rw [mem_ball, dist_eq_norm]
  calc ‖z - 2‖ ≤ |(z - 2).re| + |(z - 2).im| := norm_le_abs_re_add_abs_im _
    _ = |z.re - 2| + |z.im| := by simp
    _ < |x| + r + 2 := by
        have ha : |z.re - 2| < 2 := by rw [abs_lt]; constructor <;> linarith
        have hb : |z.im| = |t| := by rw [him]
        linarith

/-- **The variation zero-set is closed.**  It is locally finite, hence closed in ℝ. -/
theorem isClosed_badHeightSet (k : ℕ) : IsClosed (badHeightSet k) := by
  have hlf : LocallyFinite (fun t : badHeightSet k => ({(t : ℝ)} : Set ℝ)) := by
    intro x
    obtain ⟨ε, hε, hfin⟩ : ∃ ε > 0, (badHeightSet k ∩ Metric.ball x ε).Finite :=
      ⟨1, one_pos, badHeightSet_inter_ball_finite k x 1⟩
    refine ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, ?_⟩
    apply Set.Finite.subset (hfin.preimage (Subtype.val_injective.injOn))
    intro t ht
    obtain ⟨y, hy⟩ := ht
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [hy1] at hy2
    exact ⟨t.2, hy2⟩
  have hkey := hlf.isClosed_iUnion (fun t => isClosed_singleton)
  rwa [show (⋃ t : badHeightSet k, ({(t : ℝ)} : Set ℝ)) = badHeightSet k from by ext x; simp]
    at hkey

/-- **The variation zero-set is locally isolated at every ambient point.**  A sufficiently small
ball about any real `x` contains no rung-failing height other than possibly `x` itself. -/
theorem badHeightSet_isolated (k : ℕ) {x : ℝ} :
    ∃ ε > 0, ∀ y ∈ badHeightSet k, dist y x < ε → y = x := by
  classical
  have hfin : (badHeightSet k ∩ Metric.ball x 1).Finite :=
    badHeightSet_inter_ball_finite k x 1
  set F : Finset ℝ := (hfin.toFinset).filter (fun y => y ≠ x) with hF
  by_cases hFne : F.Nonempty
  · set δ : ℝ := (F.image (fun y => dist y x)).min' (hFne.image _) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_min'_iff]
      intro b hb
      obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
      rw [hF, Finset.mem_filter] at hy
      rw [← hyb]
      exact dist_pos.mpr hy.2
    refine ⟨min δ 1, lt_min hδpos one_pos, fun y hy hyx => ?_⟩
    by_contra hne
    have hyball : y ∈ Metric.ball x 1 := by
      rw [mem_ball]; exact lt_of_lt_of_le hyx (min_le_right _ _)
    have hyF : y ∈ F := by
      rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hy, hyball⟩, hne⟩
    have hge : δ ≤ dist y x :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hyF)
    exact absurd (lt_of_lt_of_le hyx (min_le_left _ _)) (not_lt.mpr hge)
  · refine ⟨1, one_pos, fun y hy hyx => ?_⟩
    by_contra hne
    exact hFne ⟨y, by
      rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hy, mem_ball.mpr hyx⟩, hne⟩⟩

/-- The zero-set is empty iff every jump is `2^k`-divisible. -/
theorem badHeightSet_eq_empty_iff (k : ℕ) :
    badHeightSet k = ∅ ↔ ∀ t : ℝ, 2 ^ k ∣ discJump t := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact forall_congr' fun t => not_not

/-- **RH as the emptiness of every variation zero-set.**  RH holds iff at every level the rung-failing
heights vanish — the boundary target reduced to discrete subsets of the line. -/
theorem rh_iff_forall_badHeightSet_empty :
    RiemannHypothesis ↔ ∀ k : ℕ, badHeightSet k = ∅ := by
  rw [rh_iff_forall_discJump_eq_zero]
  simp only [badHeightSet_eq_empty_iff]
  constructor
  · intro h k t; exact (h t) ▸ dvd_zero _
  · intro h t
    by_contra hne
    have hpos : 0 < discJump t := Nat.pos_of_ne_zero hne
    have hdvd := h (discJump t) t
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr Nat.lt_two_pow_self)

/-! ## (b) The Stieltjes content of the census profile -/

/-- **The Stieltjes content** of the census profile over `(a, b]`: the census increment, a finitely
additive `ZMod (2^k)`-valued content on the line. -/
noncomputable def censusIncrement (k : ℕ) (a b : ℝ) : ZMod (2 ^ k) :=
  censusProfile k b - censusProfile k a

/-- Additivity of the content over adjacent intervals. -/
theorem censusIncrement_add (k : ℕ) (a b c : ℝ) :
    censusIncrement k a b + censusIncrement k b c = censusIncrement k a c := by
  rw [censusIncrement, censusIncrement, censusIncrement]; ring

/-- The closed box order sum splits over a height slice. -/
theorem boxOrderSumLe_add_sdiff {a b : ℝ} (h : a ≤ b) :
    boxOrderSumLe a + ∑ z ∈ boxFinsetLe b \ boxFinsetLe a, (analyticOrderAt xi z).toNat
      = boxOrderSumLe b := by
  rw [boxOrderSumLe, boxOrderSumLe, add_comm]
  exact Finset.sum_sdiff (boxFinsetLe_mono h)

/-- **The content is the enclosed order over the slice.**  The census increment over `(a, b]` is
the total ξ-order of the zeros with height in `(a, b]`, reduced mod `2^k`. -/
theorem censusIncrement_eq_sum_sdiff {k : ℕ} {a b : ℝ} (h : a ≤ b) :
    censusIncrement k a b
      = (∑ z ∈ boxFinsetLe b \ boxFinsetLe a, (analyticOrderAt xi z).toNat : ZMod (2 ^ k)) := by
  rw [censusIncrement, censusProfile, censusProfile, ← boxOrderSumLe_add_sdiff h]
  push_cast
  ring

/-- **The atom weight of the content at a height**: the jump divisor mod `2^k`. -/
noncomputable def censusAtom (k : ℕ) (t : ℝ) : ZMod (2 ^ k) := (discJump t : ZMod (2 ^ k))

/-- **Atomicity.**  When the zeros newly enclosed by raising `a` to `b` are exactly those at a single
height `t`, the content is that height's atom. -/
theorem censusIncrement_eq_atom_of_slice {k : ℕ} {a b t : ℝ} (h : a ≤ b)
    (hslice : boxFinsetLe b \ boxFinsetLe a = (boxHeightZeros_finite t).toFinset) :
    censusIncrement k a b = censusAtom k t := by
  rw [censusIncrement_eq_sum_sdiff h, hslice, censusAtom, discJump, Nat.cast_sum]

/-- The finite-carrier Stieltjes content, from a supplied height-indexed configuration. -/
noncomputable def finiteCensusIncrement (k : ℕ) (G : ℝ → Finset ℂ) (mg : ℂ → ℕ) (a b : ℝ) :
    ZMod (2 ^ k) :=
  windowDiscBit k (G b) mg - windowDiscBit k (G a) mg

/-- **The two contents agree.**  Under the height-indexed transport data the ξ Stieltjes content
equals the finite-carrier content over every interval. -/
theorem censusIncrement_eq_finite {N k : ℕ} {G : ℝ → Finset ℂ} {mg : ℂ → ℕ}
    (hdata : TransportedProfile N k G mg) (a b : ℝ) :
    censusIncrement k a b = finiteCensusIncrement k G mg a b := by
  have hprof := censusProfile_eq_finiteCensusProfile hdata
  rw [censusIncrement, finiteCensusIncrement, congrFun hprof a, congrFun hprof b]

/-- The finite-carrier atom weight at a height. -/
noncomputable def finiteCensusAtom (k : ℕ) (H : ℝ → Finset ℂ) (mg : ℂ → ℕ) (t : ℝ) :
    ZMod (2 ^ k) := (finiteDiscJump H mg t : ZMod (2 ^ k))

/-- **The atom difference is the divisor difference mod `2^k`.**  The signed jump difference of §3,
reduced mod `2^k`, is exactly the gap between the two carriers' atom weights. -/
theorem censusAtom_sub_finite (k : ℕ) (H : ℝ → Finset ℂ) (mg : ℂ → ℕ) (t : ℝ) :
    censusAtom k t - finiteCensusAtom k H mg t = ((jumpDiff H mg t : ℤ) : ZMod (2 ^ k)) := by
  rw [censusAtom, finiteCensusAtom, jumpDiff]
  push_cast
  ring

/-- **The two atomic measures agree mod `2^k`.**  Because the divisor difference is `2^k`-valued
(`two_pow_dvd_jumpDiff`), the ξ and finite-carrier atom weights coincide in `ZMod (2^k)`: the
divisor-difference measure vanishes mod `2^k`. -/
theorem censusAtom_eq_finite {N k : ℕ} {H : ℝ → Finset ℂ} {mg : ℂ → ℕ} (t : ℝ)
    (hstrip : ∀ z ∈ H t, 0 < z.re ∧ z.re < 1)
    (hmg : ∀ z ∈ H t, (mg z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl : ∀ z ∈ H t, lineReflect z ∈ H t)
    (hD : ∑ z ∈ stripHeightFinset t, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ H t, mg z
        [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ (stripHeightFinset t).filter (fun z => z.re = 1 / 2),
          (analyticOrderAt xi z).toNat
        ≡ ∑ z ∈ (H t).filter (fun z => z.re = 1 / 2), mg z [MOD 2 ^ (k + 1)]) :
    censusAtom k t = finiteCensusAtom k H mg t := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  have hdvd := two_pow_dvd_jumpDiff (N := N) (k := k) t hstrip hmg hcl hD hL
  have hzero : ((jumpDiff H mg t : ℤ) : ZMod (2 ^ k)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  rw [← sub_eq_zero, censusAtom_sub_finite, hzero]

end RHTower
