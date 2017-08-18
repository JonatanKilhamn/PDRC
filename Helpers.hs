module Helpers where

indent :: [String] -> [String]
indent = concat . map (map ("  "++)) . map lines
-- lines . (map ("  "++)) . unlines
