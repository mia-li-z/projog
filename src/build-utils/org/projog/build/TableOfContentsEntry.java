/*
 * Copyright 2013 S Webber
 * 
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *     http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.projog.build;

/**
 * Represents an entry in {@code manual.txt}.
 */
class TableOfContentsEntry {
	/** The name to display in the link. */
	final String title;
	/** Position in documentation heirachary (e.g. 2.3) */
	final String index;
	/** The actual html file. */
	final String fileName;
	TableOfContentsEntry previous;
	TableOfContentsEntry next;

	TableOfContentsEntry(String title, String fileName, String index) {
		this.title = title;
		this.fileName = fileName;
		this.index = index;
	}
	
	boolean isHeader() {
		return fileName==null;
	}
	
	boolean isSubSection() {
		return index.indexOf('.')!=index.lastIndexOf('.');
	}
}