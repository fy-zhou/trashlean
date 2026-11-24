import Trashlean.Academic.Life

/-!
# Finite-horizon life histories and the capacity of hidden information

Every finite public history admits an exponentially large family of mutually
distinct, feasible private schedules. The construction is quantitative:
it respects temporal precedence and disjoint slots, has exact combinatorial
counts, and yields a sharp necessary size for any supplementary decoder.
-/

namespace Trashlean.Academic.Life

open Finset
noncomputable section

/-- A time strictly after every event appearing in the public log. -/
def nextTime : PublicLog → ℕ
  | [] => 0
  | (_, e) :: rest => max (academicTime e + 1) (nextTime rest)

theorem event_before_nextTime (l : PublicLog) (a : Venue × AcademicEvent)
    (ha : a ∈ l) : academicTime a.2 < nextTime l := by
  induction l with
  | nil => simp at ha
  | cons b rest ih =>
      rcases b with ⟨v, e⟩
      rcases List.mem_cons.mp ha with h | h
      · subst a
        exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact (ih h).trans_le (le_max_right _ _)

/-- Each index denotes a disjoint unit slot after the public log. -/
def slotEpisode (l : PublicLog) (i : ℕ) : Episode :=
  ⟨nextTime l + i, 1, {0, 1}, {0, 1}⟩

theorem slot_valid (l : PublicLog) (i : ℕ) :
    validEpisode (slotEpisode l i) := by
  change 0 < (1 : ℕ) ∧ 2 ≤ ({0, 1} : Finset ℕ).card ∧
    ({0, 1} : Finset ℕ) = {0, 1}
  decide

theorem slot_injective (l : PublicLog) : Function.Injective (slotEpisode l) := by
  intro i j h
  have hh := congrArg Episode.start h
  change nextTime l + i = nextTime l + j at hh
  omega

theorem slot_after_public (l : PublicLog) (a : Venue × AcademicEvent)
    (ha : a ∈ l) (i : ℕ) : academicTime a.2 < (slotEpisode l i).start := by
  have hh := event_before_nextTime l a ha
  change academicTime a.2 < nextTime l + i
  omega

theorem slots_nonoverlap (l : PublicLog) {i j : ℕ} (h : i < j) :
    (slotEpisode l i).start + (slotEpisode l i).duration ≤
      (slotEpisode l j).start := by
  change nextTime l + i + 1 ≤ nextTime l + j
  omega

def schedule (l : PublicLog) (s : Finset ℕ) : List Episode :=
  (s.sort (· ≤ ·)).map (slotEpisode l)

def scheduleHistory (l : PublicLog) (s : Finset ℕ) : History :=
  restorePublic l ++ privateSuffix (schedule l s)

@[simp] theorem schedule_public (l : PublicLog) (s : Finset ℕ) :
    publicTrace (scheduleHistory l s) = l := by
  simp [scheduleHistory]

@[simp] theorem schedule_private (l : PublicLog) (s : Finset ℕ) :
    privateTrace (scheduleHistory l s) = schedule l s := by
  simp [scheduleHistory]

theorem schedule_all_valid (l : PublicLog) (s : Finset ℕ) (e : Episode)
    (he : e ∈ schedule l s) : validEpisode e := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact slot_valid l i

theorem schedule_all_after_public (l : PublicLog) (s : Finset ℕ)
    (a : Venue × AcademicEvent) (ha : a ∈ l)
    (e : Episode) (he : e ∈ schedule l s) :
    academicTime a.2 < e.start := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact slot_after_public l a ha i

theorem schedule_nonoverlapping (l : PublicLog) (s : Finset ℕ)
    (e f : Episode) (he : e ∈ schedule l s) (hf : f ∈ schedule l s)
    (hne : e ≠ f) :
    e.start + e.duration ≤ f.start ∨ f.start + f.duration ≤ e.start := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
  have hij : i ≠ j := fun h => hne (congrArg (slotEpisode l) h)
  rcases lt_or_gt_of_ne hij with h | h
  · exact Or.inl (slots_nonoverlap l h)
  · exact Or.inr (slots_nonoverlap l h)

theorem schedule_injective (l : PublicLog) :
    Function.Injective (scheduleHistory l) := by
  intro s t h
  have he := congrArg privateTrace h
  rw [schedule_private, schedule_private] at he
  unfold schedule at he
  have hs := (List.map_injective_iff.mpr (slot_injective l)) he
  ext i
  have hi := congrArg (fun xs : List ℕ => i ∈ xs) hs
  simpa only [Finset.mem_sort] using Iff.of_eq hi

theorem schedule_BB_iff (l : PublicLog) (s : Finset ℕ) :
    CCBB (scheduleHistory l s) ↔ s.Nonempty := by
  unfold CCBB
  rw [schedule_private]
  constructor
  · rintro ⟨e, he, _⟩
    obtain ⟨i, hi, _⟩ := List.mem_map.mp he
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨slotEpisode l i, List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩,
      slot_valid l i⟩

theorem all_schedules_same_certification (l : PublicLog) (s t : Finset ℕ)
    (v : Venue) (p : ℕ) :
    Certified (scheduleHistory l s) v p ↔ Certified (scheduleHistory l t) v p := by
  apply certification_observational
  simp

/-- Every subset of n available slots gives a distinct complete history. -/
def scheduleFamily (l : PublicLog) (n : ℕ) : Finset History :=
  ((Finset.range n).powerset).image (scheduleHistory l)

theorem scheduleFamily_card (l : PublicLog) (n : ℕ) :
    (scheduleFamily l n).card = 2 ^ n := by
  rw [scheduleFamily, Finset.card_image_of_injective _ (schedule_injective l),
    Finset.card_powerset, Finset.card_range]

theorem scheduleFamily_fiber (l : PublicLog) (n : ℕ) :
    ∀ h ∈ scheduleFamily l n, publicTrace h = l := by
  intro h hh
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hh
  exact schedule_public l s

/-- Exact number when the private time budget is constrained to k slots. -/
def budgetFamily (l : PublicLog) (n k : ℕ) : Finset History :=
  ((Finset.range n).powersetCard k).image (scheduleHistory l)

theorem budgetFamily_card (l : PublicLog) (n k : ℕ) :
    (budgetFamily l n k).card = Nat.choose n k := by
  rw [budgetFamily, Finset.card_image_of_injective _ (schedule_injective l),
    Finset.card_powersetCard, Finset.card_range]

/-- A supplementary message in Fin m must distinguish all 2^n schedules
if exact recovery from the public log and this message is possible. -/
theorem leakage_capacity (l : PublicLog) (n m : ℕ)
    (leak : History → Fin m) (decode : PublicLog → Fin m → Finset ℕ)
    (correct : ∀ s ∈ (Finset.range n).powerset,
      decode (publicTrace (scheduleHistory l s)) (leak (scheduleHistory l s)) = s) :
    2 ^ n ≤ m := by
  have hi : Set.InjOn (fun s => leak (scheduleHistory l s))
      (↑((Finset.range n).powerset) : Set (Finset ℕ)) := by
    intro s hs t ht he
    have h₁ := correct s hs
    have h₂ := correct t ht
    rw [schedule_public] at h₁ h₂
    exact h₁.symm.trans ((congrArg (decode l) he).trans h₂)
  have hcard := Finset.card_le_univ
    (s := ((Finset.range n).powerset).image (fun s => leak (scheduleHistory l s)))
  rw [Finset.card_image_of_injOn hi, Finset.card_powerset,
    Finset.card_range, Fintype.card_fin] at hcard
  exact hcard

/-- The leakage bound is sharp: the schedule itself is an injective code
on the finite family. -/
theorem exact_schedule_code (l : PublicLog) (n : ℕ) :
    Nonempty (scheduleFamily l n ≃ Fin (2 ^ n)) := by
  classical
  have hcard : Fintype.card (↥(scheduleFamily l n)) = 2 ^ n := by
    simpa using scheduleFamily_card l n
  exact ⟨Fintype.equivFinOfCardEq hcard⟩

/-- The full joint encoding is injective, not just fiberwise injective. -/
def jointCode : PublicLog × Finset ℕ → History :=
  fun p => scheduleHistory p.1 p.2

theorem jointCode_injective : Function.Injective jointCode := by
  rintro ⟨l, s⟩ ⟨k, t⟩ h
  have hl := congrArg publicTrace h
  change publicTrace (scheduleHistory l s) = publicTrace (scheduleHistory k t) at hl
  rw [schedule_public, schedule_public] at hl
  subst k
  have hs : s = t := schedule_injective l h
  subst t
  rfl

theorem jointCode_public : publicTrace ∘ jointCode = Prod.fst := by
  funext p
  exact schedule_public p.1 p.2

#print axioms leakage_capacity
#print axioms scheduleFamily_card
#print axioms jointCode_injective

end
end Trashlean.Academic.Life
