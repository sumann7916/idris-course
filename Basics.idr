module Basics

namespace Days

data Day = 
    Monday
    |
    Tuesday
    |
    Wednesday
    |
    Thursday
    |
    Friday
    |
    Saturday
    |
    Sunday

%name Day day, day1, day2

nextWeekday: Day -> Day
nextWeekday Monday = Tuesday
nextWeekday Tuesday = Wednesday
nextWeekday Wednesday = Thursday
nextWeekday Thursday = Friday
nextWeekday Friday = Monday
nextWeekday Saturday = Monday
nextWeekday Sunday = Monday


